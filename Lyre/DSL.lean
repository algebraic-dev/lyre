import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra
import Lyre.Grammar
import Lyre.LR1

import Std.Data.HashSet
import Std.Data.HashMap
import Lyre.Data.HashMap
import Lyre.Data.HashSet


namespace DSL

open Lean.Elab Command Term
open Lean Parser Command
open Std


syntax (name := gClause) "|" (ident (":" ident)?)* "{" term "}" : command
syntax (name := gRule) "rule " ident ":" "{" term "}" (gClause)+ : command
syntax (name := gTkn) "token " ident ":" "{" term "}" : command
syntax (name := gGrammar) "grammar " ident "where" "start " ident "{" term "}" gTkn* gRule* : command

abbrev Acts := HashMap (String × UInt64) (List (Option String × Term) × Syntax)

abbrev DArr : (s: Nat) → (α: Type u) → Type u
  | Nat.zero,          a => Array a
  | Nat.succ Nat.zero, a => Array a
  | Nat.succ n,        a => Array (DArr n a)

def toName (name: Syntax): CommandElabM String :=
  if let some nameStr := name.isIdOrAtom?
      then pure nameStr
      else liftMacroM (Macro.throwErrorAt name "it should be a name")

def getTerminals (tkns: Array Syntax) (pats: Array Syntax): CommandElabM (HashMap String Syntax) := do
  let mut terminals: HashMap String Syntax := HashMap.empty
  for pat in pats, tkn in tkns do
    let nameStr ← toName tkn
    match terminals.find? nameStr with
    | none   => terminals := terminals.insert nameStr pat
    | some _ => liftMacroM (Macro.throwErrorAt tkn "It's already defined!")
  pure terminals

def getNonTerms (names: Array Syntax) (types: Array Syntax): CommandElabM (HashMap String Syntax) := do
  let mut nonTermsTy : HashMap String Syntax := HashMap.empty
  for name in names, ty in types do
    let nameStr ← toName name
    match nonTermsTy.find? nameStr with
    | none   => nonTermsTy := nonTermsTy.insert nameStr ty
    | some _ => liftMacroM (Macro.throwErrorAt name "It's already defined!")
  pure nonTermsTy

abbrev Dict : Type := (HashMap String Syntax × HashMap String Syntax)

def getTerm (table: Dict) (name: Syntax): CommandElabM Term := do
  let nameStr ← toName name
  match (table.fst.find? nameStr, table.snd.find? nameStr) with
  | (some _, some _) => liftMacroM (Macro.throwErrorAt name "Cannot decide")
  | (some _, none  ) => pure (Term.term nameStr)
  | (none  , some _) => pure (Term.nonTerm nameStr)
  | (none, none)     => liftMacroM (Macro.throwErrorAt name "Cannot find this term")

def transBinder (table: Dict) (alt1: Syntax) (alt2: Option Syntax): CommandElabM (Option String × Term) := do
  let (bindSyn, ruleSyn) :=
    match alt2 with
    | some ruleS => (Option.some alt1, ruleS)
    | none       => (Option.none, alt1)
  match (bindSyn, bindSyn >>= Syntax.isIdOrAtom?) with
    | (none,   _)           => getTerm table ruleSyn >>= λres => pure (none, res)
    | (some _, some binder) => getTerm table ruleSyn >>= λres => pure (Option.some binder, res)
    | (some x, none)        => liftMacroM (Macro.throwErrorAt x "Invalid name")

@[macroInline] def Option.getAlt : Option α → (α → β) → β → β
  | some x, fn, _ => fn x
  | none,   _, e  => e

def getPrimTable (table: Dict) (names: Array Syntax)
                 (alts: DArr 3 Syntax) (opts: DArr 3 (Option Syntax)) (acts: DArr 2 Syntax)
                 : CommandElabM (Array (String × Array (Array Term × Array (Option String × Term) × Syntax))) := do
   let mut resTable := #[]
   for name in names, alts' in alts, opts' in opts, acts' in acts do
      let mut clausesRes := #[]
      for clause in alts', opts'' in opts', act in acts' do
        let mut clauseRes := #[]
        let mut bindersRes := #[]
        for alt1 in clause, alt2 in opts'' do
          let (binderOpt, term') ← transBinder table alt1 alt2
          clauseRes  := clauseRes.push term'
          bindersRes := bindersRes.push (binderOpt, term')
        clausesRes := clausesRes.push (clauseRes, bindersRes, act)
      let nameRes ← toName name
      resTable := resTable.push (nameRes, clausesRes)
    pure resTable

def buildGrammarTable (st: String) (table: Array (String × Array (Array Term × Array (Option String × Term) × Syntax)))
                      : CommandElabM (Grammar × Acts) := do
  let mut gram : Grammar := ⟨st, HashMap.empty⟩
  let mut acts : Acts := HashMap.empty
  for (name, alts) in table do
    let mut ruleRes: Rule := ⟨name, HashSet.empty⟩
    for (terms, binders, act) in alts do
      acts := acts.insert (name, hash terms.toList) (binders.toList, act)
      ruleRes := ⟨name, ruleRes.rules.insert terms.toList⟩
    gram := ⟨st, gram.rules.insert name ruleRes⟩
  pure (gram, acts)

def findStart (nonTerms: HashMap String α) (st: Syntax): CommandElabM String := do
  let startName ← toName st
  match HashMap.find? nonTerms startName with
  | some _ => pure startName
  | none   => liftMacroM (Macro.throwErrorAt st s!"Cannot find this non terminal!")

def buildGrammarFromSyntax : Syntax → CommandElabM (LRTable × Acts × String × HashMap String Syntax × HashMap String Syntax × Syntax)
  | `(grammar $name where start $st { $tknTy } $[token $tkns : { $pats' }]* $[rule $names : { $ruleTypes }
     $[| $[$terms $[: $binders]?]* { $actions }]*]*) => do

    let grammarName ← toName name

    -- Terminal definition
    let terminals ← getTerminals tkns pats'
    let nonTerms ← getNonTerms names ruleTypes
    let primTable ← getPrimTable (terminals, nonTerms) names terms binders actions
    let startName ← findStart nonTerms st

    let (gram, acts) ← buildGrammarTable startName primTable

    let lrtable := compile gram

    pure (lrtable, acts, grammarName, terminals, nonTerms, tknTy)
  | stx =>
    liftMacroM (Macro.throwErrorAt stx s!"i'll syntax {stx}")

def reprAct : Action → CommandElabM Syntax
      | Action.shift n => do
        let cons ← `(Action.shift)
        pure (Syntax.mkApp cons #[Syntax.mkNumLit (toString n)])
      | Action.reduce n e => do
        let cons ← `(Action.reduce)
        pure (Syntax.mkApp cons #[Syntax.mkStrLit n, Syntax.mkNumLit (toString e)])
      | Action.accept => `(Action.accept)

def countConflicts (m: LRTable): (Nat × Nat) :=
    HashSet.fold count (0, 0) m.conflict
  where
    count : (Nat × Nat) → Action × Action → (Nat × Nat)
      | (sr, rr), (Action.reduce _ _, Action.reduce _ _) => (sr, rr + 1)
      | (sr, rr), (Action.reduce _ _, Action.shift _)  => (sr + 1, rr)
      | (sr, rr), (Action.shift _, Action.reduce _ _)  => (sr + 1, rr)
      | res, _ => res

elab gram:gGrammar : command => do
    let (table, acts, nStart, terms, nonTerms, retTy) ← buildGrammarFromSyntax gram
    let emp ← `(List.nil)
    let st ← table.action.foldM
      (λst (state', term') action => do
        let cons ← `(List.cons)
        let act ← reprAct action
        let x ← `((($(Syntax.mkNumLit (toString state')), $(Syntax.mkStrLit term')), $(act)))
        pure (Syntax.mkApp cons #[x, st]) ) emp
    let goto ← table.goto.foldM
      (λst (state', term') to => do
        let cons ← `(List.cons)
        let x ← `((($(Syntax.mkNumLit (toString state')), $(Syntax.mkStrLit term')), $(Syntax.mkNumLit (toString to))))
        pure (Syntax.mkApp cons #[x, st]) ) emp
    let macroT ← `({ states := HashMap.empty, action := HashMap.fromList $st, goto := HashMap.fromList $goto, conflict := HashSet.empty })

    let (sr, rr) := countConflicts table
    let mut phrases := ""

    if sr > 0 then phrases := s!"Found {sr} shift/reduce conflicts"
    if rr > 0 then phrases := s!"{phrases}\nFound {rr} reduce/reduce conflicts"

    if phrases != "" then liftMacroM (Macro.throwErrorAt gram phrases)

    (set_option hygiene false in `(def getLRTable: LRTable := $macroT)) >>= elabCommand

end DSL