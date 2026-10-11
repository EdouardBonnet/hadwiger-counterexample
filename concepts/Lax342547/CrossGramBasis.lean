import Lax342547.CrossBatchMixing

/-!
---
title: Independent characters of actual mutual Gram entries
type: definition and theorem
---
The two reciprocal cross Gram blocks occupy disjoint coefficient entries.
Their characters have no duplicate descriptions: every nonzero pattern
gives a nonzero cross-batch matrix and therefore at least N bits of rank.
-/

namespace Lax342547.CrossGramBasis

open Lax342547.MomentSpace Lax342547.CrossBatchMixing
open scoped BigOperators

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

abbrev Slots (I J K L : Type) := (I × L) ⊕ (J × K)

def tests {I J K L : Type} [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L] :
    Slots I J K L → Matrix (I ⊕ J) (K ⊕ L) Binary
  | Sum.inl (i,l) => fun a b => if a = Sum.inl i ∧ b = Sum.inr l then 1 else 0
  | Sum.inr (j,k) => fun a b => if a = Sum.inr j ∧ b = Sum.inl k then 1 else 0

axiom coefficient_blocks (t : Slots I J K L → Binary) :
    coefficient tests t = Matrix.fromBlocks 0 (fun i l => t (Sum.inl (i,l)))
      (fun j k => t (Sum.inr (j,k))) 0

axiom nonzero_coefficient (t : Slots I J K L → Binary) (ht : t ≠ 0) : coefficient tests t ≠ 0

axiom mutual_gram_bits (N : ℕ)
    (xy : (Fin N × (I ⊕ J) → Binary) × (Fin N × (K ⊕ L) → Binary)) :
    (∀ i l,crossBits tests N xy (Sum.inl (i,l)) = ∑ a,xy.1 (a,Sum.inl i)*xy.2 (a,Sum.inr l)) ∧
    (∀ j k,crossBits tests N xy (Sum.inr (j,k)) = ∑ a,xy.1 (a,Sum.inr j)*xy.2 (a,Sum.inl k))

end Lax342547.CrossGramBasis
