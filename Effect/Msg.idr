module Effect.Msg

import Effects
import System.Concurrency.Raw

data Actions : Type where
     DoSend : (dest : princ) -> (x : Type) -> (x -> Actions) -> Actions
     DoRecv : (src : princ) -> (x : Type) -> (x -> Actions) -> Actions
     End : Actions

data ProtoT : a -> Type where
     Proto : {x : a} -> ProtoT x 

data Msg : Type -> Effect where
     SendTo   : (p : princ) -> (val : a) ->
                { ProtoT (DoSend p a k) ==> ProtoT (k val) } Msg princ ()
     RecvFrom : (p : princ) ->
                { ProtoT (DoRecv p a k) ==> ProtoT (k result) } Msg princ a

instance Handler (Msg Ptr) IO where
     handle Proto (SendTo p v) k = do sendToThread p v
                                      k () Proto
     handle Proto (RecvFrom p) k = do test <- checkMsgs
                                      x <- getMsg
                                      k x Proto

MSG : Type -> Actions -> EFFECT
MSG t xs = MkEff (ProtoT xs) (Msg t) 

sendTo : Handler (Msg p) m =>
         (x : p) -> (val : a) ->
         { [MSG p (DoSend x a k)] ==> [MSG p (k val)] } EffM m ()
sendTo proc v = SendTo proc v

recvFrom : Handler (Msg p) m =>
           (x : p) -> 
           { [MSG p (DoRecv x a k)] ==> [MSG p (k result)] } EffM m a
recvFrom proc = RecvFrom proc


