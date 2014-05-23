-- ----------------------------------------------------------------- [ Msg.idr ]
-- The message effect.
-- --------------------------------------------------------------------- [ EOH ]
module Effect.Msg

import Effects
import System.Concurrency.Raw
import Network.Socket
import Control.IOExcept

||| Detail how to serialise data for a particular communication channel.
class Marshal val chan (m : Type -> Type) where
      ||| Marshal a value and then send using the communication channel.
      marshalSend   : chan -> val -> m ()
      ||| Receive a value from the communication channel and unmarhsal it.
      unmarshalRecv : chan -> m val

-- ------------------------------------------------------------------------------
-- Protocol actions (from perspective of one principal) 
-- ------------------------------------------------------------------------------

||| Protocol actions (from perspective of one principal) 
data Actions : Type where
     DoSend  : (dest : princ) -> (x : Type) -> (x -> Actions) -> Actions
     DoRecv  : (src : princ) -> (x : Type) -> (x -> Actions) -> Actions
     DoRec   : Inf Actions -> Actions
     End     : Actions

data Valid : p -> List (p, chan) -> Type where
     First : .{x : p} -> .{xs : List (p, chan)} -> {c : chan} ->
             Valid x ((x, c) :: xs)
     Later : .{x : p} -> .{xs : List (p, chan)} ->
             Valid x xs -> Valid x (y :: xs)

(:=) : p -> chan -> (p, chan)
(:=) x c = (x, c)

%reflection
reflectListValid : List (p, chan) -> Tactic
reflectListValid [] = Refine "First" `Seq` Solve
reflectListValid (x :: xs)
     = Try (Refine "First" `Seq` Solve)
           (Refine "Later" `Seq` (Solve `Seq` reflectListValid xs))
-- TMP HACK! FIXME!
-- The evaluator needs a 'function case' to know its a reflection function
-- until we propagate that information! Without this, the _ case won't get
-- matched. 
reflectListValid (x ++ y) = Refine "First" `Seq` Solve
reflectListValid _ = Refine "First" `Seq` Solve

%reflection
reflectValid : (P : Type) -> Tactic
reflectValid (Valid a xs)
     = reflectListValid xs `Seq` Solve

-- syntax IsValid = tactics { byReflection reflectValid; }
syntax IsValid = (| First,
                    Later First,
                    Later (Later First),
                    Later (Later (Later First)),
                    Later (Later (Later (Later First))),
                    Later (Later (Later (Later (Later First)))) |)

lookup : (xs : List (p, chan)) -> Valid x xs -> chan
lookup ((x, c) :: ys) First = c
lookup (y :: ys) (Later x) = lookup ys x

remove : (xs : List (p, chan)) -> Valid x xs -> List (p, chan)
remove ((x, c) :: ys) First = ys
remove (y :: ys) (Later x) = y :: remove ys x


-- ------------------------------------------------------------------------------
-- The CONC effect for concurrency
-- ------------------------------------------------------------------------------

data PID = MkPid Ptr

data Conc : Effect where
    Fork : PID -- Parent VM
           -> (PID -> IO ()) -- Process, given parent VM
           -> { () } Conc PID

CONC : EFFECT
CONC = MkEff () Conc

-- Get VM here so it really is the parent VM not calculated in the
-- child process!
fork : (PID -> IO ()) -> { [CONC] } Eff IO PID
fork proc = Fork (MkPid prim__vm) proc

instance Handler Conc IO where
    handle () (Fork me proc) k = do pid <- fork (proc me)
                                    k (MkPid pid) ()


-- ------------------------------------------------------------------------------
-- The MSG Effect
-- ------------------------------------------------------------------------------

-- ------------------------------------------------ [ MSG Effect Specification ]

data ProtoT : a -> List (p, chan) -> Type where
     Proto : {x : a} -> {cs : List (p, chan)} -> ProtoT x cs

using (cs : List (princ, chan))
  ||| The message data type.
  data Msg : Type -> Type -> (Type -> Type) -> Effect where
       ||| Associate a communication channel with a principle.
       |||
       ||| @p The principle to be assigned to the channel.
       ||| @c The channel being assigned.
       SetChannel : %erase x
                    {x : a} -> (p : princ) -> (c : chan) ->
                    { ProtoT x cs ==> ProtoT x ((p := c) :: cs) }
                    Msg princ chan m ()
                    
       ||| Free the communication channel from a principle.
       |||
       ||| @p The principle being freed.
       ||| @v Proof that the principle is part of the protocol.                
       DropChannel : %erase x
                     {x : a} -> (p : princ) -> (v : Valid p cs) ->
                     { ProtoT x cs ==> ProtoT x (remove cs v) }
                     Msg princ chan m ()   

       ||| Send a message to a principle in the protocol.
       |||
       ||| @p The message recipient.
       ||| @val The message to be sent.
       ||| @v Proof that the principle is part of the protocol.
       SendTo : %erase k
                Marshal a chan m =>
                  (p : princ) -> (val : a) -> (v : Valid p cs) ->
             { ProtoT (DoSend p a k') cs ==> ProtoT (k' val) cs } 
               Msg princ chan m ()
               
       ||| Receive a message from a principle in the protocol.
       |||
       ||| @p The originator of the message.
       ||| @v Proof that the principle is part of the protocol.                
       RecvFrom : %erase k
                  Marshal a chan m =>
                  (p : princ) -> (v : Valid p cs) ->
             { ProtoT (DoRecv p a k) cs ==> ProtoT (k result) cs } 
               Msg princ chan m a

       ||| Step through the protocol.
       Cont : %erase k
              { ProtoT (DoRec k) cs ==> ProtoT k cs }
              Msg princ chan m ()

-- ----------------------------------------------- [ MSG Effect Implementation ]
||| Definition of the message effect.
MSG : Type -> (Type -> Type) -> List (princ, chan) -> Actions -> EFFECT
MSG {chan} princ m ps xs = MkEff (ProtoT xs ps) (Msg princ chan m) 

||| Send a message to a principle.
|||
||| @x The recipient of the message.
||| @val The message to be sent.
sendTo : Marshal a chan m =>
         {cs : List (p, chan)} ->
         (x : p) -> 
         (val : a) ->
         {default IsValid prf : Valid x cs} ->     
         { [MSG p m cs (DoSend x a k')] ==> 
           [MSG p m cs (k' val)] } Eff m ()
sendTo proc v {prf} = SendTo proc v prf

||| Receive a message from a principle.
|||
||| @x The originator of the message.
recvFrom : Marshal a chan m => 
         {cs : List (p, chan)}
         -> (x : p)
         -> {default IsValid prf : Valid x cs}
         -> { [MSG p m cs (DoRecv x a k)] ==> 
              [MSG p m cs (k result)] } Eff m a
recvFrom proc {prf} = RecvFrom proc prf

||| Bind the protocol implementation with the associated communication channel.
|||
||| @p The principle identified in the protocol specification.
||| @c The channel being bound to the principle.
setChan : {cs : List (princ, chan)}
        -> (p : princ)
        -> (c : chan)
        -> { [MSG princ m cs xs] ==> 
             [MSG princ m ((p := c) :: cs) xs] } Eff m ()
setChan p c = SetChannel p c

||| Free the protocol implementation from the associated communication channel.
|||
||| @p The principle being freed.
dropChan : {cs : List (princ, chan)}
         -> (p : princ)
         -> {default IsValid v : Valid p cs}
         -> { [MSG princ m cs xs] ==> 
              [MSG princ m (remove cs v) xs] } Eff m ()
dropChan p {v} = DropChannel p v

||| Continue executing the protocol.
continue : {cs : List (princ, chan)} ->
        { [MSG princ m cs (DoRec k)] ==> [MSG princ m cs k] } Eff m ()
continue = Cont

syntax rec [x] = continue >>= (\_ => x)

-- ------------------------------------------------------------------------------
-- Implementation Contexts
-- ------------------------------------------------------------------------------

-- ------------------------------------------------- [ Message Passing Context ]
-- Handlers for message passing concurrency


--- Generic marshalling commands for sending data between threads.
instance Marshal a PID IO where
    marshalSend (MkPid chan) x = sendToThread chan (x, prim__vm)
    unmarshalRecv (MkPid chan) = getMsgFrom chan
        where 
          -- if the sender is not the expected sender, try again then
          -- put the message back in our queue.
          getMsgFrom : Ptr -> IO t 
          getMsgFrom {t} p = do (m, sender) <- getMsg {a = (t, Ptr)}
                                q <- eqPtr p sender
                                if q then return m
                                     else do putStrLn "RETRY"
                                             m' <- getMsgFrom p
                                             sendToThread prim__vm (m, sender)
                                             return m'
         
--- Perform the marshalling in relation to the protocol specification.
instance Handler (Msg princ PID IO) IO where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p v) k = k () Proto
  handle Proto Cont k = k () Proto

  handle (Proto {cs}) (SendTo p v valid) k 
         = do let pid = lookup cs valid
              marshalSend pid v
              k () Proto
  handle (Proto {cs}) (RecvFrom {a} p valid) k 
         = do -- test <- checkMsgs
              let pid = lookup cs valid
              k !(unmarshalRecv pid) Proto

-- ----------------------------------------------------- [ The Network Context ]
-- Handlers for sending marshalled strings over a network 

NetError : Type
NetError = String

||| Serialisation methods for data types over a network.
class Netvalue a where
  ||| Serialise data to a String representation.
  toNetString : a -> String
  ||| Deserialise a String representation into data.
  fromNetString : String -> Maybe a

-- Generic marshelling commands for data in the Network Context.
instance Netvalue a => Marshal a Socket (IOExcept String) where
  marshalSend sock v 
         = do res <- ioe_lift $ send sock (toNetString v)
              case res of
                   Left err => ioe_fail (show err)
                   Right _ => return ()

  unmarshalRecv sock
         = do inval <- ioe_lift $ recv sock 4096 -- tmp hack!
              case inval of
                   Left err => ioe_fail (show err)
                   Right (str, len) =>
                        if (len == 0) then ioe_fail "Nothing received"
                           else do case fromNetString {a} str of
                                        Nothing => ioe_fail "Invalid data"
                                        Just x => return x

-- Perform the marshalling in relation to the protocol specification.
instance Monad m => Handler (Msg princ Socket m) m where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p v) k = k () Proto
  handle Proto Cont k = k () Proto

  handle (Proto {cs}) (SendTo p v valid) k
         = do let sock = lookup cs valid
              marshalSend sock v
              k () Proto

  handle (Proto {cs}) (RecvFrom {a} p valid) k
         = do let sock = lookup cs valid
              k !(unmarshalRecv sock) Proto

-- ------------------------------------------------------------- [ IPC Context ]
-- Handlers for communicating with an external application 

||| How to serialise and deserialise a data type `a`.
class IPCValue a where
  ||| Serialise data to a String representation.
  toIPCString : a -> String
  ||| Deserialise a String representation into data.
  fromIPCString : String -> Maybe a

||| An `fget` implementation to interact with an external application.
fget : File -> IO String
fget f = do fpoll f
            fget' f
  where fget' : File -> IO String
        fget' h = case !(fgetc' h) of
                       Nothing => return ""
                       Just '\n' => return ""
                       Just c => return (strCons c !(fget' h))

-- Serialisation commands for `String` types
instance IPCValue String where
  toIPCString x   = x
  fromIPCString x = Just x

-- Generic marshalling commands for data in the IPC context.
instance IPCValue a => Marshal a File (IOExcept String) where
  marshalSend f v = do ioe_lift $ fwrite f (toIPCString v)
                       ioe_lift $ fflush f
                       
  unmarshalRecv f = do --                        x <- ioe_lift $ fpoll f
                       if not True
                         then ioe_fail "Nothing to receive"
                         else do inval <- ioe_lift $ fread f
                                 case fromIPCString {a} inval of
                                    Nothing => ioe_fail "Invalid data"
                                    Just x => return x

-- Perform the marshalling in relation to the protocol specification.
instance Monad m => Handler (Msg princ File m) m where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p c) k = k () Proto
  handle Proto Cont k = k () Proto

  handle (Proto {cs}) (SendTo p v valid) k
         = do let f = lookup cs valid
              marshalSend f v
              k () Proto

  handle (Proto {cs}) (RecvFrom {a} p valid) k
         = do let f = lookup cs valid
              k !(unmarshalRecv f) Proto


-- --------------------------------------------------------------------- [ EOF ]
