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

%reflection
reflectListElem : List a -> Tactic
reflectListElem [] = Refine "Here" `Seq` Solve
reflectListElem (x :: xs)
     = Try (Refine "Here" `Seq` Solve)
           (Refine "There" `Seq` (Solve `Seq` reflectListElem xs))
-- TMP HACK! FIXME!
-- The evaluator needs a 'function case' to know its a reflection function
-- until we propagate that information! Without this, the _ case won't get
-- matched. 
reflectListElem (x ++ y) = Refine "Here" `Seq` Solve
reflectListElem _ = Refine "Here" `Seq` Solve

%reflection
reflectElem : (P : Type) -> Tactic
reflectElem (Elem a xs)
     = reflectListElem xs `Seq` Solve

syntax IsElem = tactics { search 100; }

-- ----------------------------------------------------- [ Protocol Definition ]

using (xs : List princ)
  ||| Definition of protocol actions. 
  data Protocol : List princ -> Type -> Type where
       ||| Send data from one principal to another.
       |||
       ||| @from The message originator.
       ||| @to   The message recipient.
       ||| @a    The type of the message to be sent.
       Send' : (from : princ) -> (to : princ) -> (a : Type) ->
                Elem from xs -> Elem to xs -> Protocol xs a
       
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
         {default IsElem pf : Elem from xs} ->
         {default IsElem pt : Elem to xs} ->
         Protocol xs a
  Send from to a {pf} {pt} = Send' from to a pf pt

  -- Syntactic Sugar for specifying protocols.
  syntax [from] "==>" [to] "|" [t] = Send' from to t IsElem IsElem

  total
  mkProcess : (x : princ) -> Protocol xs ty -> (ty -> Actions) -> Actions
  mkProcess x (Send' from to ty fp tp) k with (prim__syntactic_eq _ _ x from)
    mkProcess x (Send' from to ty fp tp) k | Nothing with (prim__syntactic_eq _ _ x to)
      mkProcess x (Send' from to ty fp tp) k | Nothing | Nothing = End
      mkProcess x (Send' from x ty fp tp) k | Nothing | (Just refl) 
            = DoRecv from ty k
    mkProcess x (Send' x to ty fp tp) k | (Just refl) 
            = DoSend to ty k
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
