module Main

import Effects
import Effect.StdIO

import System.Protocol

data Command = Next | Stop 

count : Protocol ['Client, 'Server] ()
count = do cmd <- 'Client ==> 'Server | Command 
           case cmd of
              Next => do foo <- 'Server ==> 'Client | Int 
                         Rec count 
              Stop => Done

countServer : (v : Int) -> (client : PID) ->
              Process IO count 'Server ['Client := client] [] ()
countServer v client
              = do cmd <- recvFrom 'Client
                   case cmd of
                        Next => do sendTo 'Client (v * 2)
                                   rec (countServer (v + 1) client)
                        Stop => return ()

countClient : (server : PID) ->
              Process IO count 'Client ['Server := server] [STDIO] ()
countClient server = do
                 putStr "More? ('n' to stop) "
                 x <- getStr
                 case (trim x /= "n") of
                    True => do sendTo 'Server Next
                               ans <- recvFrom 'Server 
                               putStrLn (show ans)
                               rec (countClient server)
                    False => do sendTo 'Server Stop

doCount : Process IO count 'Client [] [STDIO] ()
doCount = do server <- spawn (countServer 0) []
             setChan 'Server server 
             countClient server
             dropChan 'Server

main : IO ()
main = runConc [()] doCount
