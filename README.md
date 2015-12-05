# Modified Elm Compiler

An extended abstract detailing this work has been submitted to the [POPL 2016 SRC](http://conf.researchr.org/track/POPL-2016/POPL-2016-SRC).

The main changes can be found in the `Type.Effect` modules.

State of the implementation:

- [x] Implement Constraint Generation
- [x] Worklist algorithm to solve constraints
- [x] Instantiation and Generalization
- [ ] (Almost done) Transfer annotations and constraints across modules
- [x] Fix bugs in Constructor types
- [x] Proper types for recursive values
- [x]  Implication constraints for branch results
- [ ]  Implication constraints for matched variables within branch
- [ ]  Track Control-flow along with patterns
- [ ]  Change complete pattern matches to Top
- [ ] Implement case optimizations for if expressions

Since module-support isn't there yet, this version
won't properly compile the core libraries.

To test it, clone this repository, and execute the function `Compile.compileFile "Test.elm"` where `Test.elm` is whatever
Elm file you use. Make sure that it doesn't contain
any imports or references to standard library functions.
