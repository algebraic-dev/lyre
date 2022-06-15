# Lyre
Incomplete LALR(1) DSL for Lean (that compiles to a LR Table but does not compile to lean code lol)

```lean
import Lyre.Grammar
import Lyre.LR1
import Lyre.DSL
open DSL

grammar myGrammar where

  start s { String }

  token x      : { "a" }
  token star   : { "v" }
  token eq     : { "c" }

  rule s
    :            { Int }
    | s s star   { d }
    | s s x      { x }
    | x          { e }
```
