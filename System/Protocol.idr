-- ------------------------------------------------------------ [ Protocol.idr ]
-- An effectful implementation of protocols.
-- --------------------------------------------------------------------- [ EOH ]
module System.Protocol

import Effects
import Effect.StdIO
import Effect.Msg
import Effect.Exception

%access public

using (xs : List a)
  data Elem : a -> List a -> Type where
       Here  : Elem x (x :: xs)
       There : Elem x xs -> Elem x (y :: xs)

syntax IsOK = tactics { search 100; }

-- ----------------------------------------------------- [ Protocol Definition ]

-- using (xs : List princ)
class Unit u where
      unit : u

instance Unit () where
    unit = () 

||| Checks if a send is valid, and computes the return type
|||
||| The return type tells us how the rest of the protocol can depend on
||| the value that was trasmitted. If there are only two participants,
||| clearly they both know the value, so it is safe to depend on it.
||| Otherwise, we can't depend on it, so return ().
data SendOK : (transmitted : Type) -> 
              (from : princ) -> 
              (to : princ) -> 
              (participants : List princ) -> 
              (continuation : Type) -> Type where
     SendLR : SendOK a x y [x, y] a
     SendRL : SendOK a x y [y, x] a
     SendGhost : Elem x xs -> Elem y xs -> SendOK a x y xs ()

||| Definition of protocol actions. 
data Protocol : List princ -> Type -> Type where
     ||| Send data from one principal to another.
     |||
     ||| @from The message originator.
     ||| @to   The message recipient.
     ||| @a    The type of the message to be sent.
     Send' : (from : princ) -> (to : princ) -> (a : Type) ->
             (prf : SendOK a from to xs b) -> Protocol xs b
     
     ||| Implementation of Do notation for protocols.
     (>>=) : Protocol xs a -> (a -> Protocol xs b) -> Protocol xs b

     Rec : Inf (Protocol xs a) -> Protocol xs a       
     pure : a -> Protocol xs a

||| Signify the end of a protocol.
Done : Protocol xs ()
Done = pure ()

||| Send data from one principal to another.
|||
||| @from The message originator.
||| @to   The message recipient.
||| @a    The type of the message to be sent.       
Send : (from : princ) -> (to : princ) -> (a : Type) ->
       {auto prf : SendOK a from to xs b} ->
       Protocol xs b
Send from to a {prf} = Send' from to a prf

-- Syntactic Sugar for specifying protocols.
syntax [from] "==>" [to] "|" [t] = Send' from to t IsOK

total
mkProcess : (x : princ) -> Protocol xs ty -> (ty -> Actions) -> Actions
mkProcess x (Send' from to ty (SendGhost y z)) k with (prim__syntactic_eq _ _ x from)
  mkProcess x (Send' from to ty (SendGhost y z)) k | Nothing with (prim__syntactic_eq _ _ x to)
    mkProcess x (Send' from to ty (SendGhost y z)) k | Nothing | Nothing = k () 
    mkProcess x (Send' from to ty (SendGhost y z)) k | Nothing | (Just w) = DoRecv from ty (\x => k ())
  mkProcess x (Send' from to ty (SendGhost y z)) k | (Just w) = DoSend to ty (\x => k ()) 

mkProcess {xs = [from,to]} x (Send' from to ty SendLR) k with (prim__syntactic_eq _ _ x from)
      | Nothing = DoRecv from ty k 
      | (Just y) = DoSend to ty k
mkProcess {xs = [to,from]} x (Send' from to ty SendRL) k with (prim__syntactic_eq _ _ x from)
      | Nothing = DoRecv from ty k 
      | (Just y) = DoSend to ty k

mkProcess x (y >>= f) k = mkProcess x y (\cmd => mkProcess x (f cmd) k)
mkProcess x (Rec p) k = DoRec (mkProcess x p k)
mkProcess x (pure y) k = k y

protoAs : (x : princ) -> Protocol xs () -> Actions
protoAs x p = mkProcess x p (\k => End)

-- ------------------------------------------------------- [ Protocol Contexts ]

||| Definition of effectul protocols for the network context.
Agent : {xs : List princ} ->
           Protocol xs () -> princ -> 
           List (princ, chan) ->
           List EFFECT -> Type -> Type
Agent {princ} {chan} s p ps es t
    = Eff t 
            (GEN_MSG (Direct ByProgram) ps (protoAs p s) :: es)
            (\v => GEN_MSG (Direct ByProgram) ps End :: es)

||| Definition of effectful protocols for concurrent processes.
Process : {xs : List princ} ->
           Protocol xs () -> princ -> 
           List (princ, PID) ->
           List EFFECT -> Type -> Type
Process s p ps es t = Agent s p ps (CONC :: es) t

||| Definition of effectful protocols for interprocess communication.
IPC : {xs : List princ} ->
      Protocol xs () -> princ -> 
      List (princ, File) ->
      List EFFECT -> Type -> Type
IPC s p ps es t = Eff t 
            (GEN_MSG (Via ByProgram String) ps (protoAs p s) :: es)
            (\v => GEN_MSG (Via ByProgram String) ps End :: es)

-- ------------------------------------------------------ [ Syntax Definitions ]

-- Helper syntax for spawning processes and running concurrent process.

syntax spawn [p] [rs] = fork (\parent => runInit (Proto :: () :: rs) (p parent))
syntax runConc [es] [p] = runInit (Proto :: () :: es) p
-- --------------------------------------------------------------------- [ EOF ]

