module Main

import Effects
import Effect.Default
import Effect.StdIO
import Effect.Msg

import System.Protocol

data MsgTy = SYN | SYNACK | ACK

data TCPMsg : MsgTy -> Type where
  Syn    : TCPMsg SYN
  Ack    : TCPMsg ACK
  SynAck : TCPMsg SYNACK


total
handshake : Protocol ['Alice, 'Bob] ()
handshake = do
  (_, x) <- 'Alice ==> 'Bob    | (TCPMsg SYN, Nat)
  (_, y, _) <- 'Bob ==> 'Alice | (TCPMsg SYNACK, Nat, (x' ** x' = S x))
  'Alice ==> 'Bob              | (TCPMsg ACK, (y' ** y' = S y))
  Done

covering
bob : Nat -> (client : PID)
      -> Process (handshake) 'Bob ['Alice := client] [STDIO] ()
bob seqno client = do
    (msg, x) <- recvFrom 'Alice
    let x' = S x
    putStrLn $ "Bob -> Alice: SynAck, " ++ show seqno ++ ", " ++ show x'
    sendTo 'Alice (SynAck, seqno, (x' ** Refl))
    (msg1, no') <- recvFrom 'Alice
    putStrLn $ "Received from Alice: " ++ show (getWitness no')
    pure ()

covering
alice : Nat -> (server : PID)
      -> Process (handshake) 'Alice ['Bob := server] [STDIO] ()
alice seqno server = do
    putStrLn $ "Alice -> Bob: Syn, " ++ show seqno
    sendTo 'Bob (Syn, seqno)
    (msg, y, x) <- recvFrom 'Bob
    putStrLn $ "Alice -> Bob: Ack " ++ show (S y)
    sendTo 'Bob (Ack, (S y ** Refl))
    pure ()


doHandshake : IO ()
doHandshake = runConc [()] doShake
  where
    doShake : Process (handshake) 'Alice [] [STDIO] ()
    doShake = do
       server <- spawn (bob 2) [()]
       setChan 'Bob server
       alice 100 server
       dropChan 'Bob
       pure ()

-- -------------------------------------------------------------------- [ Main ]
namespace Main
  main : IO ()
  main = doHandshake
