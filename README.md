# Modified Elm Compiler

An extended abstract detailing this work has been submitted to the [POPL 2016 SRC](http://conf.researchr.org/track/POPL-2016/POPL-2016-SRC).

The main changes can be found in the `Type.Effect` modules.

State of the implementation:

- [x] Implement Constraint Generation
- [x] Worklist algorithm to solve constraints
- [x] Instantiation and Generalization
- [ ] Fix bugs in Constructor types
- [ ] Proper types for recursive values
- [ ]  Implication constraints
- [ ]  Track Control-flow along with patterns
- [ ]  Change complete pattern matches to Top

Learn about the Elm programming language at [elm-lang.org](http://elm-lang.org/).

[![Build Status](https://travis-ci.org/elm-lang/elm-compiler.svg)](https://travis-ci.org/elm-lang/elm-compiler)

## Install

Follow [these instructions][installer] to use Elm on your machine. Be sure to use
the platform specific installers if you are on Mac or Windows. It's way easier!

 [installer]: https://github.com/elm-lang/elm-platform/blob/master/README.md#elm-platform

## Build from source / Contribute

Use [this script][build] to build the entire Elm Platform from source: the compiler,
REPL, package manager, and reactor. Be sure to read all the instructions to learn
how the script works and what your workflow will be like.

[build]: https://github.com/elm-lang/elm-platform/blob/master/installers/BuildFromSource.hs

## Help

If you are stuck, email
[the list](https://groups.google.com/forum/?fromgroups#!forum/elm-discuss)
or ask a question in the
[#Elm IRC channel](http://webchat.freenode.net/?channels=elm).
