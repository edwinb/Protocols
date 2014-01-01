module System.Protocol

import Effects
import Effect.StdIO
import Effect.Msg

using (xs : List a)
  data Elem : a -> List a -> Type where
       Here  : Elem x (x :: xs)
       There : Elem x xs -> Elem x (y :: xs)

%reflection
reflectListElem : List a -> Tactic
reflectListElem [] = Refine "Here" `Seq` Solve
reflectListElem (x :: xs)
     = Try (Refine "Here" `Seq` Solve)
           (Refine "There" `Seq` (Solve `Seq` reflectListEffElem xs))
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

syntax IsElem = tactics { byReflection reflectElem; }


using (xs : List princ)
  data Protocol : List princ -> Type -> Type where
       Send' : (from : princ) -> (to : princ) -> (a : Type) ->
               Elem from xs   -> Elem to xs -> Protocol xs a
       (>>=) : Protocol xs a -> (a -> Protocol xs b) -> Protocol xs b
       pure  : a -> Protocol xs a

  Done : Protocol xs ()
  Done = pure ()

  syntax [from] "==>" [to] "|" [t] = Send' from to t IsElem IsElem

  data SEnv : List princ -> Type where
       Nil  : SEnv {princ} []
       (::) : Maybe princ -> SEnv xs -> SEnv (x :: xs)

  lookupEnv : {xs : List princ} ->
              Elem x xs -> SEnv xs -> Maybe princ
  lookupEnv Here (x :: xs) = x
  lookupEnv (There p) (x :: xs) = lookupEnv p xs

  mkProcess : (x : princ) -> Protocol xs t -> (t -> Actions) -> Actions
  mkProcess x (Send' from to ty fp tp) k with (prim__syntactic_eq _ _ x from)
    mkProcess x (Send' from to ty fp tp) k | Nothing with (prim__syntactic_eq _ _ x to)
      mkProcess x (Send' from to ty fp tp) k | Nothing | Nothing = End
      mkProcess x (Send' from x ty fp tp) k | Nothing | (Just refl) 
            = DoRecv from ty k
    mkProcess x (Send' x to ty fp tp) k | (Just refl) 
            = DoSend to ty k
  mkProcess x (y >>= f) k = mkProcess x y (\t => mkProcess x (f t) k)
  mkProcess x (pure y) k = End

Agent : {xs : List princ} ->
           (Type -> Type) ->
           Protocol xs () -> princ -> List EFFECT -> Type -> Type
Agent {princ} m s p es t
    = EffM m t (MSG princ (mkProcess p s (\x => End)) :: es)
               (\v => MSG princ End :: es)


-- syntax Protocol [princ] [p] [c] [es] [t] =
--        EffM IO ((PROCESS princ (mkProcess c p (\x => End))) :: es)
--                (\v => (PROCESS princ End) :: es) t
         
