module Main

import Effects
import Effect.StdIO

import System.Protocol

data Command = Next | Stop

-- parameters (C : a, S : a)

%assert_total -- Need this because we need to compute with it in a type!
count : Int -> Protocol ['Client, 'Server] ()
count v = case !('Client ==> 'Server | Command) of
                Next => do 'Server ==> 'Client | (x : Int ** x = v * 2)
                           count (v + 1)
                Stop => Done

countServer : (v : Int) -> (client : PID) ->
              Process IO (count v) 'Server ['Client := client] [] ()
countServer v client
              = do t <- recvFrom 'Client 
                   case t of
                        Next => do sendTo 'Client (v * 2 ** refl)
                                   countServer (v + 1) client
                        Stop => return ()

countClient : (server : PID) ->
              Process IO (count v) 'Client ['Server := server] [STDIO] ()
countClient {v} server
            = do putStr "More? ('n' to stop) "
                 case (trim !getStr /= "n") of
                    True => do sendTo 'Server Next
                               putStrLn (show (getWitness !(recvFrom 'Server)))
                               countClient {v=v+1} server
                    False => do sendTo 'Server Stop

doCount : Process IO (count 0) 'Client [] [STDIO] ()
doCount = do server <- spawn (countServer 0) []
             setChan 'Server server
             countClient {v=0} server
             dropChan 'Server

main : IO ()
main = runConc [()] doCount
