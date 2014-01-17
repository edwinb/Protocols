module Effect.Msg

import Effects
import System.Concurrency.Raw

------------------------------------------------------------------
-- Marshaling values 
------------------------------------------------------------------

class Marshal val princ (m : Type -> Type) where
    send : val -> princ -> m ()
    receive : princ -> m val

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

  data Msg : Type -> Type -> Effect where
       SetChannel : {x : a} -> (p : princ) -> (c : chan) ->
                    { ProtoT x cs ==> ProtoT x ((p := c) :: cs) }
                    Msg princ chan ()
       DropChannel : {x : a} -> (p : princ) -> (v : Valid p cs) ->
                     { ProtoT x cs ==> ProtoT x (remove cs v) }
                     Msg princ chan ()

       SendTo   : -- Marshal a princ m =>
                  (p : princ) -> (val : a) -> Valid p cs ->
             { ProtoT (DoSend p a k) cs ==> ProtoT (k val) cs } 
               Msg princ chan ()
       RecvFrom : -- Marshal a princ m =>
                  (p : princ) -> Valid p cs ->
             { ProtoT (DoRecv p a k) cs ==> ProtoT (k result) cs } 
               Msg princ chan a

instance Marshal a PID IO where
  send val (MkPid ptr) = sendToThread ptr val
  receive (MkPid ptr) = do x <- getMsg
                           return x

instance Handler (Msg princ PID) IO where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p v) k = k () Proto

  handle (Proto {cs}) (SendTo p v valid) k 
         = do let MkPid ptr = lookup cs valid
              sendToThread ptr v 
              k () Proto
  handle (Proto {cs}) (RecvFrom {a} p valid) k 
         = do -- test <- checkMsgs
              x <- getMsg
              k x Proto

MSG : Type -> List (princ, chan) -> Actions -> EFFECT
MSG {chan} princ ps xs = MkEff (ProtoT xs ps) (Msg princ chan) 

sendTo : {cs : List (p, chan)} ->
         (x : p) -> 
         (val : a) ->
         {default IsValid prf : Valid x cs} ->     
--           (prf : Valid x cs) ->
         { [MSG p cs (DoSend x a k)] ==> 
           [MSG p cs (k val)] } Eff m ()
sendTo proc v {prf} = SendTo proc v prf

recvFrom : {cs : List (p, chan)} ->
           (x : p) -> 
           {default IsValid prf : Valid x cs} ->
           { [MSG p cs (DoRecv x a k)] ==> 
             [MSG p cs (k result)] } Eff m a
recvFrom proc {prf} = RecvFrom proc prf

setChan : {cs : List (princ, chan)} -> 
          (p : princ) -> (c : chan) ->
          { [MSG princ cs xs] ==> 
            [MSG princ ((p := c) :: cs) xs] } Eff m ()
setChan p c = SetChannel p c

dropChan : {cs : List (princ, chan)} -> 
           (p : princ) -> {default IsValid v : Valid p cs} ->
           { [MSG princ cs xs] ==> 
             [MSG princ (remove cs v) xs] } Eff m ()
dropChan p {v} = DropChannel p v

