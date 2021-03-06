# Modified Elm Compiler

Here is the [Extended Abstract](http://eremondi.com/preprints/eremondi-popl16-src.pdf) which was accepted to the POPL 2016 Student Research Competition.

The main changes can be found in the `Type.Effect` modules.

State of the implementation:

- [x] Implement Constraint Generation
- [x] Worklist algorithm to solve constraints
- [x] Instantiation and Generalization
- [ ] (Almost done) Transfer annotations and constraints across modules
- [x] Fix bugs in Constructor types
- [x] Proper types for recursive values
- [x]  Implication constraints for branch results
- [x]  Implication constraints for matched variables within branch (implemented but buggy)
- [ ]  Track Control-flow along with patterns
- [ ]  Change complete pattern matches to Top
- [ ] Implement case optimizations for if expressions
- [ ] Support for Elm's record types

Since module-support isn't there yet, this version
won't properly compile the core libraries.

To test it, clone this repository, and execute the function `Compile.compileFile "Test.elm"` where `Test.elm` is whatever
Elm file you use. Make sure that it doesn't contain
any imports or references to standard library functions.
