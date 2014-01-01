Protocols
=========

A DSL for describing and implementing communication protocols.
For example, given two parties 'A' and 'B', a protocol in which 'A' sends
a String to 'B' and receives an integer back could be described as follows:

```
aToB : Protocol [A, B] ()
atoB = do A ==> B | String
          B ==> A | Int
          Done
```

The type `Protocol xs t` describes a communication protocol between the 
parties `xs`, finally returning something of type `t`. The notation
`A ==> B | t` means that party `A` sends a value of type `t` to party B.

Implementations of the parties `A` and `B` can be achieved as follows:

```
a : Agent IO aToB A [STDIO] ()
a = do sendTo B "Hello"
       answer <- recvFrom B
       putStrLn (show answer)

b : Agent IO aToB B [STDIO] ()
b = do str <- recvFrom A
       sendTo A (length str)
```

These are programs in the 'Effects' DSL. It is a type error if either
implementation does not follow its side of the protocol correctly. Any
additional effects required (such as `STDIO` here) can also be listed.
This means that a protocol implementation can also invoke other effects,
manage state, etc, provided that the protocol operations themselves are
carried out in the correct order, and to completion.

Since `Protocol` is an embedded DSL, it follows that we can write more
complex protocols where later interactions depend on the results of earlier
interactions. For example:

```
data Command = Add | Multiply | Negate

mathsServer : Protocol [Client, Server] ()
mathsServer = do cmd <- Client ==> Server | Command
                 case cmd of
                      Add => do Client ==> Server | (Int, Int)
                                Server ==> Client | Int
                                Done
                      Multiply => 
                             do Client ==> Server | (Int, Int)
                                Server ==> Client | Int
                                Done
                      Negate =>
                             do Client ==> Server | Int
                                Server ==> Client | Int
```

How communication is handled in practice is independent of the protocol DSL,
and depends on an effect handler being implemented for a particular context.

The library currently includes an effect handler which supports communication
between concurrent processes. See `text/UtilServer` for a simple example.







