import Std.Data.HashSet
import Std.Data.HashMap

import Lyre.Data.HashMap
import Lyre.Data.HashSet

open Std

inductive Term
  | term (text : String)
  | nonTerm (text : String)
  deriving Hashable, BEq, Repr

structure Rule where
  label : String
  rules : HashSet (List Term)

structure Grammar where
  start   : String
  rules   : HashMap String Rule

instance : ToString Term where toString n := toString (repr n)

-- Generation of FIRST table


class Sizable (α : Type) where
  size : α → Int

instance [Sizable β] [BEq α] [Hashable α] : Sizable (HashMap α β) where
  size map := HashMap.fold (λx _ v => 1 + x + Sizable.size v) 0 map

instance [BEq α] [Hashable α] : Sizable (HashMap α β) where
  size map := map.size + 1

instance [BEq α] [Hashable α] : Sizable (HashSet α) where
  size m := HashSet.size m + 1

instance [Sizable α] [Sizable β] : Sizable (α × β) where
  size tuple := 1 + Sizable.size tuple.fst + Sizable.size tuple.snd

instance [Sizable α] : Sizable (List α) where
  size list := List.foldl (· + ·) 1 (List.map Sizable.size list)

instance : Sizable (List α) where
  size list := list.length

def fixPoint [Sizable α] (fuel: Nat) (sizable : α) (fn: α → α) : α :=
  match fuel with
  | Nat.zero   => sizable
  | Nat.succ n =>
      let res := fn sizable
      if Sizable.size res != Sizable.size sizable
        then fixPoint n (fn res) fn
        else res


def fulled (n: Nat) (res : α) (fn: α → α) : α :=
  match n with
  | Nat.succ n => fulled n (fn res) fn
  | Nat.zero   => res

-- Show

instance [Repr α] [BEq α] [Hashable α] : Repr (HashSet α) where
  reprPrec d _ := repr (HashSet.toList d)

instance [Repr α] [Repr β] [BEq α] [Hashable α] : Repr (HashMap α β) where
  reprPrec d _ := repr (HashMap.toList d)

-- Just a synonym

abbrev First    := HashMap String (HashSet String)
abbrev Nullable := HashSet String

def rotate : (α → β → δ → ω) → (β → δ → α → ω) := λf => (λa b c => f c a b)

def Option.on : β → (α → β) → Option α → β
  | _, fn, Option.some n => fn n
  | or, _, Option.none   => or

def addOn (k: String) (term: HashSet String) (table: First): First  :=
  match HashMap.find? table k with
  | Option.none   => HashMap.insert table k term
  | Option.some n => HashMap.insert table k (term ++ n)

def onFirst (tuple : α × β) (fn: α → ω): (ω × β) := (fn tuple.fst, tuple.snd)

def onSnd (tuple : α × β) (fn: β → ω): (α × ω) := (tuple.fst, fn tuple.snd)

def First.getTable (grammar: Grammar) : First × Nullable :=
    fixPoint 100 (HashMap.singleton grammar.start default, default) $
      λtable =>
        (rotate HashMap.fold) table grammar.rules
          (λtable name rule => HashSet.fold (foldItem name) table rule.rules)
  where
    foldItem (name: String) (table: First × Nullable) : List Term → First × Nullable
      | []                     => onSnd table (HashSet.insert · name)
      | (Term.term    x :: _)  => onFirst table (addOn name (HashSet.singleton x))
      | (Term.nonTerm x :: xs) =>
        let first := Option.on table.fst (addOn name · table.fst) (HashMap.find? table.fst x)
        if HashSet.contains table.snd x
          then foldItem name (first, table.snd) xs
          else (first, table.snd)

