import Std.Data.HashSet
open Std HashSet
open BEq (beq)

def HashSet.fromList [BEq β] [Hashable β] : List β → HashSet β
  | List.nil       => default
  | List.cons x xs => HashSet.insert (fromList xs) x

def HashSet.append [BEq β] [Hashable β] (fst: HashSet β) (snd: HashSet β) : HashSet β :=
    appendList (HashSet.toList fst) snd
  where
    appendList [BEq β] [Hashable β] : (fst: List β) → (snd: HashSet β) → HashSet β
      | List.nil, b => b
      | List.cons x xs, b => HashSet.insert (appendList xs b) x

def HashSet.map [BEq β] [Hashable β] [BEq α] [Hashable α] (fst: HashSet β) (fn: β → α) : HashSet α :=
  HashSet.fromList (List.map fn (HashSet.toList fst))

@[inline]
def HashSet.singleton [BEq α] [Hashable α] (k: α): HashSet α :=
  HashSet.insert default k

@[inline]
def Std.HashSet.foldFor [BEq α] [Hashable α] {δ : Type w} (m : HashSet α) (init : δ) (f : δ → α → δ) : δ :=
  match m with
  | ⟨ m, _ ⟩ => m.fold f init

instance [BEq β] [Hashable β] : HAppend (HashSet β) (HashSet β) (HashSet β) where
  hAppend a b := HashSet.append a b

instance [BEq β] [Hashable β] : Hashable (HashSet β) where
  hash a := hash (HashSet.toList a)

instance [BEq β] [Hashable β] : BEq (HashSet β) where
  beq a b := beq (HashSet.toList a) (HashSet.toList b)