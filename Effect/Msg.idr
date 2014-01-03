module Effect.Msg

import Effects
import System.Concurrency.Raw

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

-- TMP HACK!
syntax IsValid = (| First, Later First, Later (Later First), 
                    Later (Later (Later First)) |)

lookup : (xs : List (p, chan)) -> Valid x xs -> chan
lookup ((x, c) :: ys) First = c
lookup (y :: ys) (Later x) = lookup ys x

remove : (xs : List (p, chan)) -> Valid x xs -> List (p, chan)
remove ((x, c) :: ys) First = ys
remove (y :: ys) (Later x) = y :: remove ys x

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

       SendTo   : (p : princ) -> (val : a) -> Valid p cs ->
             { ProtoT (DoSend p a k) cs ==> ProtoT (k val) cs } 
               Msg princ chan ()
       RecvFrom : (p : princ) -> Valid p cs ->
             { ProtoT (DoRecv p a k) cs ==> ProtoT (k result) cs } 
               Msg princ chan a

instance Handler (Msg princ Ptr) IO where
  handle Proto (SetChannel p c) k = k () Proto
  handle Proto (DropChannel p v) k = k () Proto

  handle (Proto {cs}) (SendTo p v valid) k 
         = do sendToThread (lookup cs valid) v
              k () Proto
  handle (Proto {cs}) (RecvFrom p valid) k 
         = do test <- checkMsgs
              x <- getMsg
              k x Proto


MSG : Type -> List (princ, chan) -> Actions -> EFFECT
MSG {chan} princ ps xs = MkEff (ProtoT xs ps) (Msg princ chan) 

sendTo' : Handler (Msg p chan) m =>
          {cs : List (p, chan)} ->
          (x : p) -> (prf : Valid x cs) ->     
          (val : a) ->
          { [MSG p cs (DoSend x a k)] ==> 
            [MSG p cs (k val)] } EffM m ()
sendTo' proc prf v = SendTo proc v prf

recvFrom' : Handler (Msg p chan) m =>
            {cs : List (p, chan)} ->
            (x : p) -> 
            (prf : Valid x cs) ->
            { [MSG p cs (DoRecv x a k)] ==> 
              [MSG p cs (k result)] } EffM m a
recvFrom' proc prf = RecvFrom proc prf

-- TMP HACK until implicit argument/lift problem fixed...

syntax recvFrom [proc] = RecvFrom proc IsValid
syntax sendTo [proc] [v] = SendTo proc v IsValid
syntax setChan [princ] [chan] = SetChannel princ chan
syntax dropChan [princ] = DropChannel princ IsValid

