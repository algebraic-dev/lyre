import Lean.Elab.Command
import Lean.Parser.Term
import Lean.Parser.Do
import Lean.Parser.Extra

open Lean Parser Command

inductive MapImpl : Type u → Type v → Type (max u v + 1) where
  | nil  : MapImpl α β
  | node : MapImpl α β → α → β → MapImpl α β → MapImpl α β

inductive MapPath : ∀ {α : Type u} {β: Type v}, α → (MapImpl α β) → Type (max u v + 1) where
  | here    : ∀ {l r : MapImpl α β}, MapPath k (MapImpl.node l k v r)
  | inLeft  : ∀ {l r : MapImpl α β}, MapPath k l → MapPath k (MapImpl.node l o v r)
  | inRight : ∀ {l r : MapImpl α β}, MapPath k r → MapPath k (MapImpl.node l o v r)

def MapImpl.find : (map : MapImpl α β) → MapPath k₁ map → β
  | MapImpl.nil, p          => nomatch p
  | MapImpl.node l _ v r, p =>
    match p with
      | MapPath.here          => v
      | MapPath.inLeft proofₗ => find l proofₗ
      | MapPath.inRight proofᵣ => find r proofᵣ

def MapImpl.insert [Ord α] : MapImpl α β → α → β → MapImpl α β
  | MapImpl.nil,          key, val => MapImpl.node MapImpl.nil key val MapImpl.nil
  | MapImpl.node l k v r, key, val =>
    match compare key k with
    | Ordering.eq => MapImpl.node l key val r
    | Ordering.gt => MapImpl.node l k v (insert r key val)
    | Ordering.lt => MapImpl.node (insert l key val) k v r

inductive WellFormedMap {α : Type u} {β: Type v} [Ord α] : (map: MapImpl α β) → Prop where
  | wfEmpty  : WellFormedMap MapImpl.nil
  | wfInsert : ∀ { m : MapImpl α β}, WellFormedMap m → WellFormedMap (MapImpl.insert m k v)

def Map {α : Type u} {β: Type v} [Ord α] : Type (max u v + 1) := { x : MapImpl α β // WellFormedMap x }

def Map.findPath [DecidableEq α] [LT α] [DecidableRel (@LT.lt α _)] [Ord α]: (k:α) → (m:MapImpl α β) → Option (MapPath k m)
  | key, MapImpl.nil          => Option.none
  | key, MapImpl.node l kAr v r =>
    match decEq key kAr with
    | Decidable.isTrue p => Option.some (by rw [p]; exact MapPath.here)
    | _ => dite (LT.lt key kAr)
                (λ_ => Option.map MapPath.inLeft (findPath key l))
                (λ_ => Option.map MapPath.inRight (findPath key r))

-- Props tests

def beta := 
  leading_parser " whered " >> 
  many1Indent (ppLine >> ppGroup (group (ident >> Parser.optional ";")))

syntax "pizza" beta : command

def mkPackageDecl : Macro
| `(pizza whered $[$ds]*) => `(#check ata)
| stx => Macro.throwErrorAt stx "ill-formed package declaration"

def expandAttrs (attrs? : Option Syntax) : Array Syntax :=
  if let some attrs := attrs? then
    match attrs with
    | `(Term.attributes| @[$attrs,*]) => attrs
    | _ => #[]
  else
    #[]

macro (name := pizzar)
  "pizzad" spec:Command.whereStructInst : command => mkPackageDecl spec


pizzad whered a := b