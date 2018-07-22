# FsMiniMAL

An interpreter of OCaml/F# like programing language, designed for .NET application embedded purposes, inplemented in F#.

## Getting Started

To run REPL, open the solution on Visual Studio and start FsMiniMAL.Console project.

## Language features

The language supports most common features of OCaml/F#.

- Basic types (int, char, float, bool, string, array, list, option, ref)
- Expressions and Patterns
- Defining new value and function (with type inference)
- Hiding of types and values
- Defining new types (record type, variant type, type abbreviation)
- Defining new exception case

## Interpreter features

- Sandboxing
- Interop with F#
-- Automatic conversion from/to F# typed values
-- Automatic wrapper for F# functions

## Sandboxing

When embedding an interpreter into an application, sandboxing is necessary feature. The term sandboxing is vague. So here I create the definition for this project.

1. Any user code can not execute actions which is disallowed by host application.
2. Any user code can not crash or freeze the host application.

This interpreter have features to support above goals.

### Protection from stack overflow

The evaluation stack of the interpreter is pure F# data (not CLR stack). Therefore, it can stop excecution safely when stack overflow is detected.

### Protection from infinite loop

The interpreter counts cycles consumed and stops safely when it timed out.

### Preventing long running script freezing application

The interpreter runs as coroutine. The application may run the interpreter for specified small period of time (time slice) and stop, and then process the user event, and restart iterpreter.

Therefore it is possible to provide "stop" button on the GUI that stops running script. (If we were using CLR stack to evaluate script, this is not possible.)

### Protection from excessive memory usage

The interpreter counts all memory allocation by user code. When it reaches limit, the interpreter stops safely.

The memory counter is increased by interpreter when new object is created, and decreased by finalizer called by CLR GC when the object is freed.

### Protection from malicious attempt by user code

User code can only call the functions that is provided as builtins by the host application.

If the application developper registered unsafe functions (e.g. function for manipulating files, or start external process.) to the interpreter, it becomes unsafe.

## The drawback of sandboxing

There is drawback of the sandboxing feature. That is, the interpreter is slower than normal CLR thread.

## Acknowledgments

This project is derived from [MiniMAL](https://www.math.nagoya-u.ac.jp/~garrigue/minimal/) project.