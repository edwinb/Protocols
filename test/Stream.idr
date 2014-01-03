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

countServer : Int -> (client : PID) ->
              Process IO count Server [Client := client] [] ()
countServer x client
              = do t <- recvFrom Client 
                   case t of
                        Next => do sendTo Client x
                                   countServer (x + 1) client
                        Stop => return ()

countClient : (server : PID) ->
              Process IO count Client [Server := server] [STDIO] ()
countClient server
            = do putStr "More? ('n' to stop) "
                 case (trim !getStr /= "n") of
                    True => do sendTo Server Next
                               putStrLn (show !(recvFrom Server))
                               countClient server
                    False => do sendTo Server Stop

doCount : Process IO count Client [] [STDIO] ()
doCount = do server <- spawn (countServer 0) []
             setChan Server server
             countClient server
             dropChan Server

main : IO ()
main = runConc [()] doCount
