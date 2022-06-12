import Lyre.Grammar
import Lyre.LR1

import Std.Data.HashSet
import Std.Data.HashMap

import Lyre.Data.HashMap
import Lyre.Data.HashSet

open Grammar
open Std

def grammar : Grammar :=
  { start := "S"
  , rules := HashMap.fromList
      [ ("S", { label := "S", rules := HashSet.fromList
                  [[Term.nonTerm "Y", Term.nonTerm "Z"]
                  ,[Term.term "x"]]})
      , ("Y", { label := "Y", rules := HashSet.fromList
                  [[Term.term "z"]
                  ,[Term.term "k"]
                  ,[]]})
      , ("Z", { label := "Z", rules := HashSet.fromList
                  [[Term.term "y"]
                  ,[Term.nonTerm "L"]]})
      , ("L", { label := "L", rules := HashSet.fromList
                  [[Term.term "o"]]})
      ]
  }

def grammar2 : Grammar :=
  { start := "S"
  , rules := HashMap.fromList
      [ ("S", { label := "S", rules := HashSet.fromList
                  [[Term.nonTerm "V", Term.term "=", Term.nonTerm "E"]
                  ,[Term.nonTerm "E"]]})
      , ("E", { label := "E", rules := HashSet.fromList
                  [[Term.nonTerm "V"]]})
      , ("V", { label := "V", rules := HashSet.fromList
                  [[Term.term "x"]
                  ,[Term.term "*", Term.nonTerm "E"]]})
      ]
  }

def firstGrammar : First × Nullable := First.getTable grammar

def closureTable (grammar: Grammar) : HashSet Item :=
  let terms  := [Term.nonTerm grammar.start, Term.term "$"]
  let rule   := {label := "Start", rules := HashSet.fromList [terms]}
  let start  := Rule.toItem rule (HashSet.fromList ["$"]) terms
  let tables := First.getTable grammar
  closure grammar (tables.fst) (HashSet.fromList [start])

#eval compile grammar2