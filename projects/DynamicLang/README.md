# Exploring Dynamic Types in Haskell

##Description
Using the Dynamic and Typeable implementation as described in ["A Reflection on Types"](https://www.seas.upenn.edu/~sweirich/papers/wadlerfest2016.pdf), Simon Peyton Jones, et al. I implemented a simple dynamic language *Lang*. As the language is dynamically typed there are many unnecessary types casts. Therefore I implement *StaticLang*, a statically typed language which we can compile Lang to, omiting as many dynamic checks as we can. StaticLang is incapable of inferring the type of bound variables or the argument to a lambda. So a second iteration using nameless representation for bound variables, *LangSnl* is implemented. Unfortunately, I couldn't implement a compiler from Lang -> LangSnl. This work is based on code given to me by Stephanie Weirich.

## Making
This Haskell project uses Stack, the command `stack build` **won't work** as there is a [bug] (https://ghc.haskell.org/trac/ghc/ticket/12242) in the compiler preventing DynamicLang.hs from building. This bug will be fixed in GHC 8.0.2. To play around with the code simply use `stack ghci`.

## Files of interest.
0. Library Code files.
..* DataDynamic.hs : Implementation of dynamic types in Haskell.
..* DataTypeable.hs : Implementation of new Typeable class.
1. *Lang* files.
..* Lang.hs : Language description for Lang.
..* Eval.hs : Evaluator for Lang.
..* Parser.hs : Convenience parser for Lang terms. See report.pdf for language syntax.
..* LangTest.hs : Example programs and evaluator unit testing.
..* ParserTests.hs : Example syntax and parser unit testing.
2. *StaticLang* files.
..* StaticLang.hs : Language description for Lang.
..* StaticEval.hs : Evaluator for Dynamic
..* StaticLangTests.hs : Example programs and evaluator unit testing.
..* PrettyPrint.hs : Pretty printer for StaticLang. Implemented as show instance.
3. *LangSnl* files.
..* LangSnl.hs : Language description and evaluator for LangSnl.hs
..* LangSnlTests.hs : Simple examples of LangSnl.
4. Other files.
..* Compiler.hs : Compiler from Lang to StaticLang.
..* CompileLangSnl.hs : Compiler from Lang to LangSnl, does not work :/
..* CompilerTests.hs : Compiler.hs usage examples and unit tester.
..* Common.hs : Common functions and types shared across multiple modules.