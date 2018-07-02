# FsMiniMAL

An interpreter of OCaml/F# like programing language, designed for .NET application embedded purposes, inplemented in F#.

## Getting Started

To run REPL, open the solution on Visual Studio and start FsMiniMAL.Console project.

## Language features

- Basic types (int, float, bool, immutable string, array, list, option, ref)
- Variant type
- Record type
- Exception type
- etc.

## Sandboxing

When embedding an interpreter into an application, sandboxing is necessary feature. The term sandboxing is vague. So here I create the definition for this project.

1. Any user code can not execute actions which is prohibited by host application.
2. Any user code can not crash or freeze the host application.

This interpreter have features to support above goals.

### Protection from stack overflow

The evaluation stack of the interpreter is pure F# data (not CLR stack). Therefore, it can stop excecution safely when stack overflow is detected.

### Protection from infinite loop

The interpreter counts cycles consumed and stops safely when it timed out.

### Protection from excessive memory usage

The interpreter counts all memory allocation by user code. When it reaches limit, the interpreter stops safely.

The memory counter is increased by interpreter when new object is created, and decreased by finalizer called by CLR GC when the object is freed.

### Protection from malicious attempt by user code

User code can only call the functions that is provided as builtins by the host application. There is no automatic interop for CLR.

## The drawback of sandboxing

There is drawback of the sandboxing feature. That is, the interpreter is extremely slow.

## Acknowledgments

This project is derived from [MiniMAL](https://www.math.nagoya-u.ac.jp/~garrigue/minimal/) project.