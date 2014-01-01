module Main

import Effects
import Effect.StdIO

import System.Protocol

data Command = Reverse | Add 

parameters (Client : Ptr, Server : Ptr)
 
  -- Describe a client/server protocol, to be run concurrently
  -- A ==> B | t    ... means "A sends a value of type t to B"

  -- In this one, a client either asks a server to reverse a string or
  -- add two numbers

  util : Protocol [Client, Server] ()
  util = do val <- Client ==> Server | Command
            case val of
               Reverse => do 
                 Client ==> Server | String
                 Server ==> Client | String
                 Done 
               Add => do 
                 Client ==> Server | Int
                 Client ==> Server | Int
                 Server ==> Client | Int
                 Done

  -- Calculate the type relative to the server and implement something which
  -- follows the protocol, verified by the MSG effect

  runServer : Agent IO util Server [STDIO] ()
  runServer = do cmd <- recvFrom Client
                 putStrLn "SERVER: Got command"
                 case cmd of
                      Reverse => do str <- recvFrom Client
                                    putStrLn ("SERVER: Reversing " ++ str)
                                    sendTo Client (reverse str)
                      Add => do x <- recvFrom Client
                                y <- recvFrom Client
                                putStrLn ("SERVER: Adding " ++ show (x, y))
                                sendTo Client (x + y) 

  -- Ditto for a client 

  runClient : Agent IO util Client [STDIO] ()
  runClient = do putStr "Command: "
                 x <- getStr
                 case (parse x) of
                      Left x => do sendTo Server Reverse
                                   sendTo Server x
                                   res <- recvFrom Server
                                   putStrLn ("CLIENT: Got " ++ res)
                      Right (x, y) =>
                                do sendTo Server Add
                                   sendTo Server x
                                   sendTo Server y
                                   res <- recvFrom Server
                                   putStrLn ("CLIENT: Got " ++ show res)
    where parse : String -> Either String (Int, Int)
          parse xs = case words xs of
                          [x, y] => Right (cast x, cast y)
                          _ => Left xs

-- We have a handler for the MSG effect which sends messages between
-- threads. We could also, for example, write a handler which send data
-- across a network (throwing an exception if the protocol was violated at
-- run-time e.g. with some ill-formed message).

-- To run the thing, run each effectful program telling 'runClient' and 
-- 'runServer' what the client/server VM pointers are (null as a placeholder 
-- for itself)

loop : Ptr -> IO ()
loop me = do server <- fork (run [MkVal _, ()] (runServer me null))
             run [MkVal _, ()] (runClient null server)
             loop me

main : IO ()
main = loop prim__vm




