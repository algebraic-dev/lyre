import Lyre.Grammar

import Std.Data.HashSet
import Std.Data.HashMap
import Lyre.Data.HashSet

open Std

structure Item where
  label : String
  terms : List Term
  index : Nat
  ahead : HashSet String
  deriving BEq, Hashable, Inhabited

def toText : Term -> String
  | Term.term x => x
  | Term.nonTerm x => x

def List.split : Nat → List α → (List α × List α)
  | Nat.zero, xs          => ([], xs)
  | Nat.succ _, []        => ([], [])
  | Nat.succ n, (x :: xs) =>
      let (bef, after) := split n xs
      (x :: bef, after)

def List.intercalateM [HAppend n n n] : List n → n → n → n
  | [],  _, empty   => empty
  | [x], _,  _      => x
  | (x :: xs), j, e => x ++ j ++ (intercalateM xs j e)

instance : Repr Item where
  reprPrec item _ :=
    let (before, after) := List.split item.index item.terms
    item.label ++ " -> " ++
      (List.intercalateM (List.map toText before) " " "") ++ "." ++
      (List.intercalateM (List.map toText after) " " "") ++ " / " ++
      (List.intercalateM (HashSet.toList item.ahead) " " "")

instance : Sizable Item where
  size item := 1 + (Sizable.size item.terms) + (Sizable.size item.ahead)

abbrev State      := HashSet Item
abbrev Transition := Nat × Term × Nat
abbrev Hash       := UInt64

inductive Action where
  | shift  (toRule: Nat)
  | reduce (on: String) (action: Hash)
  | accept
  deriving BEq, Hashable, Repr

structure LRTable where
  states   : HashMap State Nat
  action   : HashMap (Nat × String) Action
  goto     : HashMap (Nat × String) Nat
  conflict : HashSet (Action × Action)
  deriving Repr

def LRTable.addAction (table: LRTable) (key: Nat × String) (act: Action): LRTable :=
  match (HashMap.find? table.action key, act) with
  | (none, act) =>
      { table with action := HashMap.insert table.action key act }
  | (some r@(Action.shift _), Action.reduce _ _) =>
      { table with conflict := HashSet.insert table.conflict (r, act) }
  | (some other, act) =>
      { table with conflict := HashSet.insert table.conflict (other, act)
                 , action   := HashMap.insert table.action key act }

def LRTable.addGoto (table: LRTable) (key: Nat × String) (act: Nat): LRTable :=
  { table with goto := HashMap.insert table.goto key act }

def Option.getPanic [Inhabited α] : Option α → α
  | Option.some n => n
  | Option.none   => panic! "Oh no!"

def List.catOption : List (Option α) → List α
  | Option.some n :: xs => n :: (catOption xs)
  | Option.none   :: xs => catOption xs
  | [] => []

def Rule.toItem (rule: Rule) (ahead : HashSet String) (terms: List Term) : Item :=
  { label := rule.label, terms := terms, index := 0, ahead := ahead }

def Item.next? (item : Item) : Option Item :=
  if item.index > item.terms.length
    then Option.none
    else Option.some { item with index := item.index + 1 }

def Item.locus? (item: Item): Option Term := List.get? item.terms item.index

def Item.nextLocus? (item: Item): Option Term := item.next? >>= Item.locus?

def Item.withoutLook (item: Item): (String × List Term × Nat) := (item.label, item.terms, item.index)

def Item.removeLook (item: Item) : Item := { item with ahead := HashSet.empty }

def normalize (items: List Item): State :=
  let normalMap := HashMap.fromList $ List.map (λitem => (item.withoutLook, (HashSet.empty : HashSet String))) items
  let withLook  := (rotate List.foldl) normalMap items $ λmap item =>
    let key := item.withoutLook
    match HashMap.find? map key with
    | Option.some n => HashMap.insert map key (item.ahead ++ n)
    | Option.none   => HashMap.insert map key (item.ahead)
  HashMap.fold (λset (label, terms, index) ahead => set.insert { label, terms, index, ahead }) HashSet.empty withLook

def closure (grammar: Grammar) (first: First) (items: State): State :=
    normalize $ HashSet.toList $
      fixPoint 100 items $ λitems' =>
        HashSet.fold foldItem items' items'
  where
    foldItem (items: State) (item: Item): State :=
      match item.locus? with
      | Option.none | Option.some (Term.term _) => items
      | Option.some (Term.nonTerm term) =>
        let lookahead :=
          match item.nextLocus? with
          | Option.some (Term.term x)       => HashSet.singleton x
          | Option.some (Term.nonTerm term) => HashMap.findD first term default
          | Option.none                     => item.ahead
        match HashMap.find? grammar.rules term with
        | Option.some rule => items ++ HashSet.map rule.rules (Rule.toItem rule lookahead ·)
        | Option.none      => items

def gotoOn (grammar: Grammar) (first: First) (items: State) (onItem: Term): State :=
    closure grammar first (HashSet.fold foldItem HashSet.empty items)
  where
    foldItem (newItems: State) (item: Item): State :=
      match (item.locus?, item.next?) with
      | (Option.some term, Option.some newItem) =>
        if term == onItem
          then HashSet.insert newItems newItem
          else newItems
      | _ => newItems


def List.insertBy : (α → α → Ordering) → α → List α → List α
  | _  , x, []          => [x]
  | cmp, x, (y :: ys)   =>
    match cmp x y with
    | Ordering.gt => y :: insertBy cmp x ys
    | _           => x :: y :: ys

def List.sortBy (fn: α → α → Ordering) (l:List α): List α := List.foldr (insertBy fn) [] l

def toLALR (table: HashMap State Nat × HashSet Transition): HashMap State Nat × HashSet Transition :=
    let mapper :=
      HashMap.toList table.fst
      |> List.sortBy compareState
      |> List.groupBy (λx y => compareState x y == Ordering.eq)
      |> List.map mapper
      |> List.foldl List.append []
      |> HashMap.fromList
    (HashMap.fromList (filter mapper $ HashMap.toList table.fst), HashSet.map table.snd (mapTransition mapper))
  where
    compareState (f: State × Nat) (s: State × Nat): Ordering :=
      compare (hash $ HashSet.map f.fst Item.removeLook) (hash $ HashSet.map s.fst Item.removeLook)

    mapper : (List (State × Nat)) → List (Nat × Nat)
      | []        => []
      | (x :: xs) => List.map (λstate => (state.snd, x.snd)) xs

    mapTransition (mapper: HashMap Nat Nat) (trans: Transition) : Transition :=
      (HashMap.findD mapper trans.fst trans.fst, trans.snd.fst, HashMap.findD mapper trans.snd.snd trans.snd.snd)

    filter (mapper: HashMap Nat Nat) (states: List (State × Nat)) : List (State × Nat) :=
      List.filter (λ(_, n) => Option.isNone (HashMap.find? mapper n)) states

def getReductions (states: HashMap State Nat): HashSet (Nat × Item) :=
  HashMap.foldFor states default $ λreds state stateIdx =>
    HashSet.foldFor state reds $ λreds item =>
      match item.locus? with
      | Option.some _ => reds
      | Option.none   => HashSet.insert reds (stateIdx, item)

def compile (grammar: Grammar): LRTable :=
    let terms  := [Term.nonTerm grammar.start, Term.term "$"]
    let rule   := {label := "start", rules := HashSet.fromList [terms]}
    let start  := Rule.toItem rule (HashSet.fromList ["$"]) terms

    let (first, _) := First.getTable grammar

    -- Now we start to make the state for building this thing lol.
    let states := HashMap.singleton (closure grammar first (HashSet.fromList [start])) 0
    let transitions := (HashSet.empty : HashSet Transition)

    let (states, transitions) : (HashMap (HashSet Item) Nat × HashSet Transition) :=
      fixPoint 100 (states, transitions) (mkTrans first ·)

    let (states, transitions) := toLALR (states, transitions)
    let reductions := getReductions states
    let initialTable: LRTable := ⟨states, HashMap.empty, HashMap.empty, HashSet.empty⟩

    let lrTable :=
      HashSet.foldFor transitions initialTable $ λtable (from', under , to') =>
        match under with
        | Term.nonTerm x => table.addGoto   (from', x) to'
        | Term.term x    => table.addAction (from', x) (Action.shift to')

    HashSet.foldFor reductions lrTable $ λtable (on, item) =>
      HashSet.foldFor item.ahead table $ λtable term =>
        match (term, item.label) with
        | ("$", "start") => table.addAction (on, term) (Action.accept)
        | _              => table.addAction (on, term) (Action.reduce (item.label) (hash item.terms))

  where
    mkTrans (first: First) (tables: HashMap (HashSet Item) Nat × HashSet Transition): HashMap (HashSet Item) Nat × HashSet Transition :=
      HashMap.foldFor tables.fst tables $ λtables state fromStateIdx =>
        HashSet.foldFor state tables $ λ(states, transitions) item =>
          match item.locus? with
          | Option.some x =>
            let newState   := gotoOn grammar first state x
            let stateTable := HashMap.insertIfNot states newState (states.size)
            let toStateIdx := Option.getPanic $ HashMap.find? stateTable newState
            ( stateTable, HashSet.insert transitions (fromStateIdx, x, toStateIdx))
          | Option.none  =>
            (states, transitions)
