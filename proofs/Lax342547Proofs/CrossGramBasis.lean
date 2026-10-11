import Lax342547.CrossGramBasis
import Lax342547.SlotWalsh

namespace Lax342547Proofs.CrossGramBasis

open Lax342547.MomentSpace Lax342547.CrossGramBasis Lax342547.CrossBatchMixing
open Lax342547.SlotWalsh
open scoped BigOperators

variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

/--
---
conclusion: Lax342547.CrossGramBasis.coefficient_blocks
---
-/
theorem coefficient_blocks (t : Slots I J K L → Binary) :
    coefficient tests t = Matrix.fromBlocks 0 (fun i l => t (Sum.inl (i,l)))
      (fun j k => t (Sum.inr (j,k))) 0 := by
  ext (i | j) (k | l) <;>
    simp [coefficient,tests,Fintype.sum_sum_type,Fintype.sum_prod_type,ite_and,mul_ite,smul_eq_mul,
      eq_comm,Finset.sum_ite_irrel,Matrix.sum_apply,Matrix.smul_apply,Matrix.add_apply,Matrix.zero_apply,Matrix.fromBlocks]

/--
---
conclusion: Lax342547.CrossGramBasis.nonzero_coefficient
---
-/
theorem nonzero_coefficient (t : Slots I J K L → Binary) (ht : t ≠ 0) : coefficient tests t ≠ 0 := by
  intro hz
  apply ht
  funext s
  cases s with
  | inl p =>
    have h := congrArg (fun M : Matrix (I ⊕ J) (K ⊕ L) Binary => M (Sum.inl p.1) (Sum.inr p.2)) hz
    simpa [Lax342547.CrossGramBasis.coefficient_blocks,Matrix.fromBlocks] using h
  | inr p =>
    have h := congrArg (fun M : Matrix (I ⊕ J) (K ⊕ L) Binary => M (Sum.inr p.1) (Sum.inl p.2)) hz
    simpa [Lax342547.CrossGramBasis.coefficient_blocks,Matrix.fromBlocks] using h

/--
---
conclusion: Lax342547.CrossGramBasis.mutual_gram_bits
---
-/
theorem mutual_gram_bits (N : ℕ)
    (xy : (Fin N × (I ⊕ J) → Binary) × (Fin N × (K ⊕ L) → Binary)) :
    (∀ i l,crossBits tests N xy (Sum.inl (i,l)) = ∑ a,xy.1 (a,Sum.inl i)*xy.2 (a,Sum.inr l)) ∧
    (∀ j k,crossBits tests N xy (Sum.inr (j,k)) = ∑ a,xy.1 (a,Sum.inr j)*xy.2 (a,Sum.inl k)) := by
  constructor
  · intro i l
    rw [crossBits,Lax342547.SlotWalsh.bit_evaluation]
    simp [tests,Fintype.sum_sum_type,ite_and,ite_mul,Finset.sum_ite_irrel]
  · intro j k
    rw [crossBits,Lax342547.SlotWalsh.bit_evaluation]
    simp [tests,Fintype.sum_sum_type,ite_and,ite_mul,Finset.sum_ite_irrel]

end Lax342547Proofs.CrossGramBasis
