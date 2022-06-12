import Std.Data.HashMap
open Std HashMap
open BEq (beq)

def HashMap.fromList [BEq α] [Hashable α] : List (α × β) → HashMap α β
  | List.nil       => default
  | List.cons x xs => HashMap.insert (fromList xs) x.fst x.snd

def HashMap.append [BEq α] [Hashable α] (fst: HashMap α β) (snd: HashMap α β) : HashMap α β :=
    appendList (HashMap.toList fst) snd
  where
    appendList [BEq α] [Hashable α] : (fst: List (α × β)) → (snd: HashMap α β) → HashMap α β
      | List.nil, b => b
      | List.cons x xs, b => HashMap.insert (appendList xs b) x.fst x.snd

@[inline]
def HashMap.foldFor [BEq α] [Hashable α] {δ : Type w} (m : HashMap α β) (init : δ) (f : δ → α → β → δ) : δ :=
  match m with
  | ⟨ m, _ ⟩ => m.fold f init

def HashMap.insertIfNot [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  match HashMap.find? m a with
  | Option.none   => HashMap.insert m a b
  | Option.some _ => m

def HashMap.singleton [BEq α] [Hashable α] (k: α) (v: β) : HashMap α β :=
  HashMap.insert default k v

instance [BEq α] [Hashable α] : HAppend (HashMap α β) (HashMap α β) (HashMap α β) where
  hAppend a b := HashMap.append a b

instance [BEq α] [Hashable α] [Hashable β] : Hashable (HashMap α β) where
  hash a := hash (HashMap.toList a)

instance [BEq α] [BEq β] [Hashable α] [Hashable β] : BEq (HashMap α β) where
  beq a b := beq (HashMap.toList a) (HashMap.toList b)