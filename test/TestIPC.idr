module Main

import Effects
import Effect.StdIO
import Effect.Default

import System.Protocol

--------------------------------------------------------------------
-- Data/commands and marshaling
--------------------------------------------------------------------

data Command = Mod Int | Add Int Int

instance Show Command where
  show (Mod x) = "MOD " ++ show x
  show (Add x y) = show x ++ " " ++ show y

instance Marshal Command String where
  marshal (Mod max) = OK $ "MOD " ++ show max ++ "\n"
  marshal (Add x y) = OK $ show x ++ " " ++ show y ++ "\n"

  unmarshal x = case words x of
                         ["MOD", x] => OK (Mod (cast x))
                         [x, y] => OK (Add (cast x) (cast y))
                         _ => Err InvalidData

instance Marshal (x : Int ** so (x < r)) String where
    marshal (x ** _) = OK $ show x
    unmarshal {r} str = let v : Int = cast str in
                            case (choose (v < r)) of
                                 (Left p) => OK (v ** p)
                                 (Right p) => Err InvalidData

--------------------------------------------------------------------
-- Program specification
--------------------------------------------------------------------

%assert_total
prog : Int -> Protocol ['User, 'Program] ()
prog range
     = do 'Program ==> 'User | String
          case !('User ==> 'Program | Command) of
               Mod m => do 'Program ==> 'User | String
                           prog m
               Add x y => do 'Program ==> 'User | (x : Int ** so (x < range))
                             prog range

data Username = Fred | Invalid

instance Marshal Username String where
  marshal Fred = OK "Fred\n"
  marshal Invlaid = OK "invalid"

  unmarshal _ = Err InvalidData

%assert_total
login : Protocol ['User, 'Program] ()
login = do 'Program ==> 'User | String
           case !('User ==> 'Program | Username) of
                Fred => prog 10
                Invalid => Done

--------------------------------------------------------------------
-- Program wrapper
--------------------------------------------------------------------

runProg : File -> (m : Int) -> IPC (prog m) 'User [] [STDIO] ()
runProg p m = do setChan 'Program p
                 putStr !(recvFrom 'Program)
                 cmd <- readCmd
                 sendTo 'Program cmd
                 case cmd of
                      Mod m => do putStr $ "Reply: " ++ !(recvFrom 'Program)
                                  dropChan 'Program
                                  runProg p m
                      Add x y => do (resp ** prf) <- recvFrom 'Program
                                    putStrLn $ "Answer: " ++ show resp
                                    dropChan 'Program
                                    runProg p m

     where readCmd : { [STDIO] } Eff Command
           readCmd = case unmarshal {ty=Command} !getStr of
                          OK cmd => return cmd
                          Err e => do putStrLn "Bad command"
                                      putStr "Try again: "
                                      readCmd
runLogin : File -> IPC login 'User [] [STDIO] ()
runLogin p = do setChan 'Program p
                putStr !(recvFrom 'Program)
                nm <- getStr
                let uname = if (trim nm == "Fred") then Fred else Invalid
                sendTo 'Program uname
                case uname of
                     Fred => do dropChan 'Program
                                runProg p 10
                     Invalid => do dropChan 'Program
                                   return ()

main : IO ()
main = do p <- popen "perl ./test.pl" ReadWrite
          ioe_run (runInit [Proto, ()] (runLogin p))
                  (\err : MsgError => putStrLn $ "It went wrong")
                  (\ok => putStrLn "Success")
          pclose p
