module Main

import Effects
import Effect.StdIO

import System.Protocol

data Command = Next | Stop

parameters (C : Ptr, S : Ptr)

  %assert_total -- Need this because we need to compute with it in a type!
  count : Protocol [C, S] ()
  count = do cmd <- C ==> S | Command
             case cmd of
                  Next => do S ==> C | Int
                             count
                  Stop => Done

  countServer : Int -> Agent IO count S [] ()
  countServer x = do cmd <- recvFrom C
                     case cmd of
                          Next => do sendTo C x
                                     countServer (x + 1)
                          Stop => return ()

  countClient : Agent IO count C [STDIO] ()
  countClient = do putStr "More? ('n' to stop) "
                   x <- getStr
                   if (trim x /= "n")
                      then do sendTo S Next
                              num <- recvFrom S
                              putStrLn (show num)
                              countClient
                      else do sendTo S Stop
                              return ()

doCount : Ptr -> IO ()
doCount me = do server <- fork (run [Proto] (countServer me null 0))
                run [Proto, ()] (countClient null server)

main : IO ()
main = doCount prim__vm
