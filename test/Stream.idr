module Main

import Effects
import Effect.StdIO
import Effect.Msg

import System.Protocol

data Command = Next | SetIncrement | Stop

instance Default Command where
  default = Stop

gcInfo : String -> IO String
gcInfo x = do mkForeign (FFun "idris_gcInfo" [] FUnit)
              pure x

count : Protocol ['Client, 'Server] ()
count = do cmd <- 'Client ==> 'Server | Command
           case cmd of
              Next => do 'Server ==> 'Client | Int
                         Rec count
              SetIncrement => do 'Client ==> 'Server | Int
                                 Rec count
              Stop => Done

covering
countServer : (c : Int) -> (v : Int) -> (inc : Int) -> (client : PID) ->
              Process count 'Server ['Client := client] [] ()
countServer c v inc client
        = do cmd <- recvFrom 'Client -- | fail
             case cmd of
                    Next => do () <- sendTo 'Client v -- | fail
                               rec (countServer 0 (v + inc) inc client)
                    SetIncrement => do i <- recvFrom 'Client -- | fail
                                       rec (countServer 0 v i client)
                    Stop => pure ()

covering
countClient : (server : PID) ->
              Process count 'Client ['Server := server] [STDIO] ()
countClient server = do
                 putStr "More? ('n' to stop) "
                 x <- getStr
                 case (trim x /= "n") of
                    True => let xval : Int = cast (trim x) in
                                case xval /= 0 of
                                     True => do
                                       sendTo 'Server SetIncrement -- | fail
                                       sendTo 'Server xval -- | fail
                                       rec (countClient server)
                                     False => do
                                       sendTo 'Server Next -- | fail
                                       ans <- recvFrom 'Server -- | fail
                                       putStrLn (show ans)
                                       rec (countClient server)
                    False => do sendTo 'Server Stop -- | fail
                                pure ()

-- doNothing : Protocol ['Client, 'Server] ()
-- doNothing = Done

-- foo : (server : File) -> Agent' {chan=File} doNothing 'Client [] [STDIO] ()
-- foo s = do setChan 'Server s
--            dropChan 'Server -- {v = First}
-- --            return ()

doCount : Process count 'Client [] [STDIO] ()
doCount = do server <- spawn (countServer 0 0 1) []
             setChan 'Server server
             countClient server
             dropChan 'Server

main : IO ()
main = runConc [()] doCount
