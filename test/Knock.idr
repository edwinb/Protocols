module Knock

import Effects
import Effect.Default
import Effect.StdIO
import Effect.Msg

import System.Protocol

Lit : String -> Type
Lit msg = (m ** m = msg)

data KnockRes : Maybe String -> Type where
  Resp    : (a : String) -> String -> KnockRes (Just a)
  RespNew : String -> KnockRes Nothing

instance Show (KnockRes x) where
  show (Resp a x)  = unwords [a, x]
  show (RespNew x) = x

total
knock : Bool -> Protocol ['A, 'B] ()
knock b = do
  'A ==> 'B | Lit "Knock Knock"
  'B ==> 'A | Lit "Who's there?"
  res <- 'A ==> 'B | String
  'B ==> 'A | Lit (res ++ " who?")
  case b of
    True  => 'A ==> 'B | KnockRes (Just res)
    False => 'A ==> 'B | KnockRes Nothing
  Done

-- ---------------------------------------------------------- [ Client Process ]
covering
knocker : String -> String -> (knee : PID)
        -> Process (knock True) 'A ['B := knee] [STDIO] ()
knocker setup reveal knee = do
    sendTo 'B ("Knock Knock" ** Refl)

    (res ** _) <- recvFrom 'B
    putStrLn $ "From Mark: " ++ res

    sendTo 'B setup

    (res' ** _) <- recvFrom 'B
    putStrLn $ "From Mark: " ++ res'

    sendTo 'B (Resp setup reveal)

covering
knockee : (knocker : PID)
        -> Process (knock False) 'B ['A := knocker] [STDIO] ()
knockee client = do
    (kk ** _ ) <- recvFrom 'A
    putStrLn $ "From Teller: " ++ kk

    sendTo 'A ("Who's there?" ** Refl)

    res <- recvFrom 'A
    putStrLn $ "From Teller: " ++ res

    sendTo 'A ((res ++ " who?") ** Refl)

    putStrLn $ "From Teller: " ++ show !(recvFrom 'A)


-- ------------------------------------------------------ [ Sample Innvocation ]

||| Sample Innvocation of the Echo protocols between the client and
||| server functions.
covering
doKnockKnock : String -> String -> IO ()
doKnockKnock setup reveal = runConc [()] (doKnock setup reveal)
  where
    doKnock : String -> String
            -> Process (knock True) 'A Nil [STDIO] ()
    doKnock s r = do
       k <- spawn (knockee) [()]
       setChan 'B k
       knocker s r k
       dropChan 'B


-- -------------------------------------------------------------------- [ Main ]
namespace Main
  main : IO ()
  main = doKnockKnock "A mos" "Quito"

-- --------------------------------------------------------------------- [ EOF ]
