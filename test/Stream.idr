module Main

import Effects
import Effect.StdIO

import System.Protocol

data Command = Next | Stop

-- parameters (C : a, S : a)

-- %assert_total -- Need this because we need to compute with it in a type!
count : Nat -> Int -> Protocol ['Client, 'Server] ()
count (S k) x 
        = do cmd <- 'Client ==> 'Server | Command 
             case cmd of
                Next => do foo <- 'Server ==> 'Client | Int -- (val : Int ** val = v * 2)
                           count k (x + 1)
                Stop => Done
count Z x = Done

countServer : (v : Int) -> (client : PID) ->
              Process IO (count k v) 'Server ['Client := client] [] ()
countServer {k=S k} v client
              = do t <- recvFrom 'Client 
                   case t of
                        Next => do sendTo 'Client (v * 2) --  ** refl)
                                   countServer {k} (v + 1) client
                        Stop => return ()

countClient : (server : PID) ->
              Process IO (count k val) 'Client ['Server := server] [STDIO] ()
countClient {k = S k} {val} server = with Effects do
                 foom <- putStr "More? ('n' to stop) "
                 x <- getStr
                 case (trim x /= "n") of
                    True => do blarg <- sendTo 'Server Next
                               ans <- recvFrom 'Server 
                               putStrLn (show ans)
                               countClient {k} {val=val+1} server
                    False => do sendTo 'Server Stop

doCount : (k : Nat) -> Process IO (count k 0) 'Client [] [STDIO] ()
doCount k
        = do server <- spawn (countServer {k} 0) []
             setChan 'Server server 
             countClient {k} {val=0} server
             dropChan 'Server

main : IO ()
main = runConc [()] (doCount 100)

