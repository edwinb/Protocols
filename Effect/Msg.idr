module Effect.Msg

import Effects
import System.Concurrency.Raw
import Network.Socket
import Control.IOExcept

class Marshal val chan (m : Type -> Type) where
      marshalSend   : chan -> val -> m ()
      unmarshalRecv : chan -> m val

------------------------------------------------------------------
-- Protocol actions (from perspective of one principal) 
------------------------------------------------------------------

data Actions : Type where
     DoSend : (dest : princ) -> (x : Type) -> (x -> Actions) -> Actions
     DoRecv : (src : princ) -> (x : Type) -> (x -> Actions) -> Actions
     End : Actions

data Valid : p -> List (p, chan) -> Type where
     First : {x : p} -> {xs : List (p, chan)} ->
             Valid x ((x, c) :: xs)
     Later : {x : p} -> {xs : List (p, chan)} ->
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


------------------------------------------------------------------
-- The CONC effect
------------------------------------------------------------------

data PID = MkPid Ptr

data Conc : Effect where
    Fork : PID -- ^ Parent VM
           -> (PID -> IO ()) -- ^ Process, given parent VM
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

------------------------------------------------------------------
-- The MSG effect
------------------------------------------------------------------

data ProtoT : a -> List (p, chan) -> Type where
     Proto : {x : a} -> {cs : List (p, chan)} -> ProtoT x cs

-- Idea: parameterise by labels and channel type, allow setting channels,
-- can only send/receive on a known channel.

using (cs : List (princ, chan))

  data Msg : Type -> Type -> (Type -> Type) -> Effect where
       SetChannel : %erase x
                    {x : a} -> (p : princ) -> (c : chan) ->
                    { ProtoT x cs ==> ProtoT x ((p := c) :: cs) }
                    Msg princ chan m ()    
       DropChannel : %erase x
                     {x : a} -> (p : princ) -> (v : Valid p cs) ->
                     { ProtoT x cs ==> ProtoT x (remove cs v) }
                     Msg princ chan m ()   

       SendTo   : %erase k
                  Marshal a chan m =>
                  (p : princ) -> (val : a) -> Valid p cs ->
             { ProtoT (DoSend p a k) cs ==> ProtoT (k val) cs } 
               Msg princ chan m ()
       RecvFrom : %erase k
                  Marshal a chan m =>
                  (p : princ) -> Valid p cs ->
             { ProtoT (DoRecv p a k) cs ==> ProtoT (k result) cs } 
               Msg princ chan m a

MSG : Type -> (Type -> Type) -> List (princ, chan) -> Actions -> EFFECT
MSG {chan} princ m ps xs 
    = MkEff (ProtoT xs ps) (Msg princ chan m) 

sendTo : Marshal a chan m =>
         {cs : List (p, chan)} ->
         (x : p) -> 
         (val : a) ->
         {default IsValid prf : Valid x cs} ->     
--           (prf : Valid x cs) ->
         { [MSG p m cs (DoSend x a k)] ==> 
           [MSG p m cs (k val)] } Eff m ()
sendTo proc v {prf} = SendTo proc v prf

recvFrom : Marshal a chan m =>
           {cs : List (p, chan)} ->
           (x : p) -> 
           {default IsValid prf : Valid x cs} ->
           { [MSG p m cs (DoRecv x a k)] ==> 
             [MSG p m cs (k result)] } Eff m a
recvFrom proc {prf} = RecvFrom proc prf

setChan : {cs : List (princ, chan)} -> 
          (p : princ) -> (c : chan) ->
          { [MSG princ m cs xs] ==> 
            [MSG princ m ((p := c) :: cs) xs] } Eff m ()
setChan p c = SetChannel p c

dropChan : {cs : List (princ, chan)} -> 
           (p : princ) -> {default IsValid v : Valid p cs} ->
           { [MSG princ m cs xs] ==> 
             [MSG princ m (remove cs v) xs] } Eff m ()
dropChan p {v} = DropChannel p v


-------------------------------------------------
-- Handlers for message passing concurrency
-------------------------------------------------

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
         

instance Handler (Msg princ PID IO) IO where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p v) k = k () Proto

  handle (Proto {cs}) (SendTo p v valid) k 
         = do let pid = lookup cs valid
              marshalSend pid v
              k () Proto
  handle (Proto {cs}) (RecvFrom {a} p valid) k 
         = do -- test <- checkMsgs
              let pid = lookup cs valid
              k !(unmarshalRecv pid) Proto

------------------------------------------------------------
-- Handlers for sending marshalled strings over a network 
------------------------------------------------------------

NetError : Type
NetError = String

class Netvalue a where
  toNetString : a -> String
  fromNetString : String -> Maybe a

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

instance Monad m => Handler (Msg princ Socket m) m where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p v) k = k () Proto

  handle (Proto {cs}) (SendTo p v valid) k
         = do let sock = lookup cs valid
              marshalSend sock v
              k () Proto

  handle (Proto {cs}) (RecvFrom {a} p valid) k
         = do let sock = lookup cs valid
              k !(unmarshalRecv sock) Proto


