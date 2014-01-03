module Main

import Effects
import Effect.StdIO

import System.Protocol

data Command = Next | Stop

-- parameters (C : a, S : a)

data Client : Type where
data Server : Type where

%assert_total -- Need this because we need to compute with it in a type!
count : Protocol [Client, Server] ()
count = case !(Client ==> Server | Command) of
             Next => do Server ==> Client | Int
                        count
             Stop => Done

countServer : Handler (Msg Type Ptr) IO => 
              (client : Ptr) -> Int -> 
              Agent IO count Server [Client := client] [] ()
countServer client x 
              = do t <- recvFrom Client 
                   case t of
                        Next => do sendTo Client x
                                   countServer client (x + 1)
                        Stop => return ()

countClient : Handler (Msg Type Ptr) IO => 
              (server : Ptr) ->
              Agent IO count Client [Server := server] [STDIO] ()
countClient server
            = do putStr "More? ('n' to stop) "
                 if (trim !getStr /= "n")
                    then do sendTo Server Next
                            putStrLn (show !(recvFrom Server))
                            countClient server
                    else do sendTo Server Stop

doCount : Ptr -> IO ()
doCount me = do server <- fork (run [Proto] (countServer me 0))
                run [Proto, ()] (countClient server)

main : IO ()
main = doCount prim__vm
