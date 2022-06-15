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

import Std.Data.HashSet
import Std.Data.HashMap

import Lyre.Data.HashMap
import Lyre.Data.HashSet