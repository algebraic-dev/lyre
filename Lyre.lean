import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra
import Lyre.Grammar
import Lyre.LR1
import Lyre.DSL

open Lean Parser Command
open Lean.Elab Command Term
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

#print getLRTable