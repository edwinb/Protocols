-- ----------------------------------------------------------------- [ Msg.idr ]
-- The message effect.
-- --------------------------------------------------------------------- [ EOH ]
module Effect.Msg

import Effects
import System.Concurrency.Raw
import Network.Socket
import Control.IOExcept

data MsgError = Timeout | InvalidData

data FailMode = ByAction | ByProgram

data TransportMode = Direct FailMode
                   | Via FailMode Type 

data CanFail : TransportMode -> Type where
     DirectFail : CanFail (Direct ByAction)
     ViaFail : CanFail (Via f t)

failMode : TransportMode -> FailMode
failMode (Direct fm) = fm 
failMode (Via fm t) = fm

data MsgResult : Type -> Type where
     OK : a -> MsgResult a
     Err : MsgError -> MsgResult a

MsgResult' : FailMode -> Type -> Type
MsgResult' ByAction x = MsgResult x
MsgResult' ByProgram x = x

class Marshal ty trans where 
      marshal   : ty -> MsgResult trans
      unmarshal : trans -> MsgResult ty

instance Marshal String String where
      marshal x = OK x 
      unmarshal x = OK x 

instance Marshal Int String where
      marshal x = OK (show x) 
      unmarshal x = OK (cast x) 

class Everything a where

instance Everything a where

marshalClass : Type -> TransportMode -> Type
marshalClass a (Direct fm) = Everything a
marshalClass a (Via fm trans) = Marshal a trans

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
fork : (PID -> IO ()) -> { [CONC] } Eff PID
fork proc = call $ Fork (MkPid prim__vm) proc

instance Handler Conc IO where
    handle () (Fork me proc) k = do pid <- fork (proc me)
                                    k (MkPid pid) ()


-- ------------------------------------------------------------------------------
-- The MSG Effect
-- ------------------------------------------------------------------------------

-- ------------------------------------------------ [ MSG Effect Specification ]

data ProtoT : Actions -> List (p, chan) -> Type where
     Proto : {cs : List (p, chan)} -> ProtoT x cs

send_cont : princ -> (a -> Actions) -> a -> MsgResult' fm () -> Actions
send_cont {fm = ByProgram} p k val x = k val
send_cont {fm = ByAction} p k val (OK x) = k val
send_cont {fm = ByAction} {a} p k val (Err x) = DoSend p a k

recv_cont : princ -> (a -> Actions) -> MsgResult' fm a -> Actions
recv_cont {fm = ByProgram} p k x = k x
recv_cont {fm = ByAction} p k (OK x) = k x
recv_cont {fm = ByAction} {a} p k (Err x) = DoRecv p a k

using (cs : List (princ, chan))
  ||| The message data type.
  data Msg : TransportMode -> Type -> Effect where
       ||| Associate a communication channel with a principle.
       |||
       ||| @p The principle to be assigned to the channel.
       ||| @c The channel being assigned.
       SetChannel : (p : princ) -> (c : chan) ->
                    { ProtoT x cs ==> ProtoT x ((p := c) :: cs) }
                    Msg tm chan ()

       ||| Free the communication channel from a principle.
       |||
       ||| @p The principle being freed.
       ||| @v Proof that the principle is part of the protocol.
       DropChannel : (p : princ) -> (v : Valid p cs) ->
                     { ProtoT x cs ==> ProtoT x (remove cs v) }
                     Msg tm chan () 

       ||| Send a message to a principle in the protocol.
       |||
       ||| @p The message recipient.
       ||| @val The message to be sent.
       ||| @prf Proof that the principle is part of the protocol.
       SendTo : marshalClass a tm =>
             (p : princ) -> (val : a) -> (prf : Valid p cs) ->
             { ProtoT (DoSend p a k') cs ==> 
               {send_ok} ProtoT (send_cont {fm=failMode tm} p k' val send_ok) cs }
               Msg tm chan (MsgResult' (failMode tm) ())

       ||| Receive a message from a principle in the protocol.
       |||
       ||| @p The originator of the message.
       ||| @v Proof that the principle is part of the protocol.
       RecvFrom : marshalClass a tm => 
             (p : princ) -> (v : Valid p cs) ->
             { ProtoT (DoRecv p a k) cs ==> 
               {rcv_ok} ProtoT (recv_cont {fm=failMode tm} p k rcv_ok) cs }
               Msg tm chan (MsgResult' (failMode tm) a)

       ||| Step through the protocol.
       Cont : { ProtoT (DoRec k) cs ==> ProtoT k cs }
              Msg tm chan ()

       ||| Give up due to error
       Abandon : CanFail tm -> MsgError -> 
                 { ProtoT k cs ==> ProtoT k' cs }
                 Msg tm chan (MsgResult' (failMode tm) ())

-- ----------------------------------------------- [ MSG Effect Implementation ]
||| Definition of the message effect.
GEN_MSG : TransportMode -> List (princ, chan) -> Actions -> EFFECT
GEN_MSG {chan} tm ps xs = MkEff (ProtoT xs ps) (Msg tm chan)

||| Definition of the message effect.
MSG : List (princ, chan) -> Actions -> EFFECT
MSG {chan} ps xs = GEN_MSG (Direct ByAction) ps xs

||| Definition of the concurrency message effect (no failure).
CONC_MSG : List (princ, chan) -> Actions -> EFFECT
CONC_MSG {chan} ps xs = GEN_MSG (Direct ByProgram) ps xs

using (tm : TransportMode)
  ||| Send a message to a principle.
  |||
  ||| @x The recipient of the message.
  ||| @val The message to be sent.
  sendTo : marshalClass a tm =>
         {cs : List (p, chan)} ->
         (x : p) ->
         (val : a) ->
         {auto prf : Valid x cs} ->
         { [GEN_MSG tm cs (DoSend x a k')] ==>
           {send_ok} [GEN_MSG tm cs (send_cont {fm=failMode tm} x k' val send_ok)] } 
         Eff (MsgResult' (failMode tm) ())
  sendTo proc v {prf} = call $ SendTo proc v prf

  ||| Receive a message from a principle.
  |||
  ||| @x The originator of the message.
  recvFrom : marshalClass a tm =>
            {cs : List (p, chan)}
         -> (x : p)
         -> {auto prf : Valid x cs}
         -> { [GEN_MSG tm cs (DoRecv x a k)] ==>
              {rcv_ok} [GEN_MSG tm cs (recv_cont {fm=failMode tm} x k rcv_ok)] } 
            Eff (MsgResult' (failMode tm) a)
  recvFrom proc {prf} = call $ RecvFrom proc prf

||| Bind the protocol implementation with the associated communication channel.
|||
||| @p The principle identified in the protocol specification.
||| @c The channel being bound to the principle.
setChan : {cs : List (princ, chan)}
        -> (p : princ)
        -> (c : chan)
        -> { [GEN_MSG fm cs xs] ==>
             [GEN_MSG fm ((p := c) :: cs) xs] } Eff ()
setChan p c = call $ SetChannel p c

||| Free the protocol implementation from the associated communication channel.
|||
||| @p The principle being freed.
dropChan : {cs : List (princ, chan)}
         -> (p : princ)
         -> {auto v : Valid p cs}
         -> { [GEN_MSG fm cs xs] ==>
              [GEN_MSG fm (remove cs v) xs] } Eff ()
dropChan p {v} = call $ DropChannel p v

||| Continue executing the protocol.
continue : {cs : List (princ, chan)} ->
        { [GEN_MSG fm cs (DoRec k)] ==> [GEN_MSG fm cs k] } Eff ()
continue = call $ Cont

abandon : {cs : List (princ, chan)} -> 
          {auto prf : CanFail tm} ->
          {p': _} ->
          MsgError -> 
          { [GEN_MSG tm cs p] ==> [GEN_MSG tm cs p'] } 
          Eff (MsgResult' (failMode tm) ())
abandon {prf} e = call $ Abandon prf e

fail : {cs : List (princ, chan)} -> 
       {auto prf : CanFail tm} ->
       { [GEN_MSG tm cs p] ==> [GEN_MSG tm cs p'] } 
       Eff (MsgResult' (failMode tm) ())
fail {prf} = call $ Abandon prf InvalidData

syntax rec [x] = continue >>= (\_ => x)

-- ------------------------------------------------------------------------------
-- Implementation Contexts
-- ------------------------------------------------------------------------------

-- ------------------------------------------------- [ Message Passing Context ]
-- Handlers for message passing concurrency

--- Perform the marshalling in relation to the protocol specification.
instance Handler (Msg (Direct ByAction) PID) (IOExcept MsgError) where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p v) k = k () Proto
  handle Proto Cont k = k () Proto
  handle Proto (Abandon DirectFail e) k = ioe_fail e

  handle (Proto {cs}) (SendTo pr v valid) k
         = do let MkPid pid = lookup cs valid
              ioe_lift $ sendToThread pid (v, prim__vm)
              k (OK ()) Proto
  handle (Proto {cs}) (RecvFrom {a} p valid) k
         = do -- test <- checkMsgs
              let MkPid pid = lookup cs valid
              k (OK !(getMsgFrom pid)) Proto
        where
          -- if the sender is not the expected sender, try again then
          -- put the message back in our queue.
          getMsgFrom : Ptr -> IOExcept MsgError t
          getMsgFrom {t} p = do (m, sender) <- ioe_lift $ getMsg {a = (t, Ptr)}
                                q <- ioe_lift $ eqPtr p sender
                                if q then return m
                                     else do ioe_lift $ putStrLn "RETRY"
                                             m' <- getMsgFrom p
                                             ioe_lift $ sendToThread prim__vm (m, sender)
                                             return m'

instance Handler (Msg (Direct ByProgram) PID) IO where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p v) k = k () Proto
  handle Proto Cont k = k () Proto
  handle Proto (Abandon DirectFail e) k impossible

  handle (Proto {cs}) (SendTo p v valid) k
         = do let MkPid pid = lookup cs valid
              sendToThread pid (v, prim__vm)
              k () Proto
  handle (Proto {cs}) (RecvFrom {a} p valid) k
         = do -- test <- checkMsgs
              let MkPid pid = lookup cs valid
              k !(getMsgFrom pid) Proto
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


{-
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

-- Generic marshalling commands for data in the Network Context.
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
-}

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

{-
-- Serialisation commands for `String` types
instance IPCValue String where
  toIPCString x   = x ++ "\n"
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
-}

-- Perform the marshalling in relation to the protocol specification.
instance Handler (Msg (Via ByProgram String) File) (IOExcept MsgError) where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p c) k = k () Proto
  handle Proto Cont k = k () Proto
  handle Proto (Abandon _ e) k = ioe_fail e

  handle (Proto {cs}) (SendTo p v valid) k
         = do let f = lookup cs valid
              let x : MsgResult String = marshal v -- FIXME: Idris bug!
              case x of
                   OK str => do ioe_lift $ fwrite f str
                                ioe_lift $ fflush f
                                k () Proto
                   Err e => ioe_fail e

  handle (Proto {cs}) (RecvFrom {a} p valid) k
         = do let f = lookup cs valid
              x <- ioe_lift $ fpoll f
              if not True
                 then ioe_fail Timeout
                 else do inval <- ioe_lift $ fread f
                         case unmarshal {ty=a} inval of
                              Err e => ioe_fail e
                              OK val => k val Proto
-- --------------------------------------------------------------------- [ EOF ]

