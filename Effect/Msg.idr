module Effect.Msg

import Effects
import System.Concurrency.Raw

data Actions : Type where
     DoSend : (dest : princ) -> (x : Type) -> (x -> Actions) -> Actions
     DoRecv : (src : princ) -> (x : Type) -> (x -> Actions) -> Actions
     End : Actions

data Val : a -> Type where
     MkVal : (x : a) -> Val x 

data Msg : Type -> Effect where
     SendTo   : (p : princ) -> (val : a) ->
                { Val (DoSend p a k) ==> Val (k val) } Msg princ ()
     RecvFrom : (p : princ) ->
                { Val (DoRecv p a k) ==> Val (k result) } Msg princ a

instance Handler (Msg Ptr) IO where
     handle (MkVal _) (SendTo p v) k = do sendToThread p v
                                          k () (MkVal _)
     handle (MkVal _) (RecvFrom p) k = do test <- checkMsgs
                                          x <- getMsg
                                          k x (MkVal _)

MSG : Type -> Actions -> EFFECT
MSG t xs = MkEff (Val xs) (Msg t) 

sendTo : Handler (Msg p) m =>
         (x : p) -> (val : a) ->
         { [MSG p (DoSend x a k)] ==> [MSG p (k val)] } EffM m ()
sendTo proc v = SendTo proc v

recvFrom : Handler (Msg p) m =>
           (x : p) -> 
           { [MSG p (DoRecv x a k)] ==> [MSG p (k result)] } EffM m a
recvFrom proc = RecvFrom proc


