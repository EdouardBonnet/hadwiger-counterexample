import Lax342547.KernelWitness
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Lax342547Proofs.KernelWitness

open Lax342547.MomentSpace
open scoped ENNReal

/--
---
conclusion: Lax342547.KernelWitness.exists_kernel_witness
---
Take the first min(q, dim ker A) vectors of a kernel basis and pad the
remaining columns with zero. The independent submatrix certifies rank.
-/
theorem exists_kernel_witness {I N : Type} [Fintype I] [Fintype N]
    (A : Matrix N I Binary) (q : ℕ) :
    ∃ C : Matrix I (Fin q) Binary, A * C = 0 ∧
      min q (Module.finrank Binary (LinearMap.ker A.mulVecLin)) ≤ C.rank := by
  classical
  let S := LinearMap.ker A.mulVecLin
  let s := min q (Module.finrank Binary S)
  have hsq : s ≤ q := min_le_left _ _
  have hsd : s ≤ Module.finrank Binary S := min_le_right _ _
  let b := Module.finBasis Binary S
  let D : Matrix I (Fin s) Binary := fun i j => (b (Fin.castLE hsd j)).val i
  have hD : Function.Injective D.mulVec := by
    apply Matrix.mulVec_injective_iff.mpr
    exact (b.linearIndependent.comp (Fin.castLE hsd) (Fin.castLE_injective hsd)).map'
      S.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hrank : D.rank = s := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hD, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  let C : Matrix I (Fin q) Binary := fun i j => if hj : j.val < s then D i ⟨j.val, hj⟩ else 0
  have hsub : C.submatrix id (Fin.castLE hsq) = D := by
    ext i j
    simp [C, Matrix.submatrix]
  refine ⟨C, ?_, ?_⟩
  · ext n j
    change (∑ i, A n i * C i j) = 0
    by_cases hj : j.val < s
    · have h := (b (Fin.castLE hsd ⟨j.val, hj⟩)).property
      change A.mulVec (b (Fin.castLE hsd ⟨j.val, hj⟩)).val = 0 at h
      simpa only [Matrix.mul_apply, C, dif_pos hj, D, Matrix.mulVec, dotProduct,
        Matrix.zero_apply, Pi.zero_apply] using congrFun h n
    · simp [C, hj]
  · have h := Matrix.rank_submatrix_le C id (Fin.castLE hsq)
    rw [hsub, hrank] at h
    exact h

theorem le_sum_min {Comp : Type} [Fintype Comp] (a : Comp → ℕ) (q : ℕ)
    (h : q ≤ ∑ e, a e) : q ≤ ∑ e, min q (a e) := by
  classical
  by_cases he : ∃ e, q ≤ a e
  · obtain ⟨e, he⟩ := he
    have hb := Finset.single_le_sum (f := fun e => min q (a e))
      (fun e _ => Nat.zero_le _) (Finset.mem_univ e)
    rwa [min_eq_left he] at hb
  · have he' (e : Comp) : a e ≤ q := Nat.le_of_lt (lt_of_not_ge (fun h => he ⟨e, h⟩))
    simpa only [fun e => min_eq_right (he' e)] using h

/--
---
conclusion: Lax342547.KernelWitness.exists_family_witness
---
Truncating each kernel dimension at q preserves a summed lower bound q.
Choose the bounded-column kernel certificate in every component.
-/
theorem exists_family_witness {Comp I N : Type} [Fintype Comp] [Fintype I] [Fintype N]
    (A : Comp → Matrix N I Binary) (q : ℕ)
    (hq : q ≤ ∑ e, Module.finrank Binary (LinearMap.ker (A e).mulVecLin)) :
    ∃ C : Comp → Matrix I (Fin q) Binary, (∀ e, A e * C e = 0) ∧ q ≤ ∑ e, (C e).rank := by
  choose C hC hrank using fun e => Lax342547.KernelWitness.exists_kernel_witness (A e) q
  exact ⟨C, hC, (le_sum_min _ q hq).trans (Finset.sum_le_sum (fun e _ => hrank e))⟩

/--
---
conclusion: Lax342547.KernelWitness.coefficient_count
---
Each binary coefficient entry has two choices. There are |Comp|*|I|*q
entries, independently of the ambient image dimension.
-/
theorem coefficient_count {Comp I : Type} [Fintype Comp] [Fintype I] (q : ℕ) :
    Nat.card (Comp → Matrix I (Fin q) Binary) = 2 ^ (Fintype.card Comp * Fintype.card I * q) := by
  change Nat.card (Comp → I → Fin q → Binary) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fun]
  simp [Binary, Nat.card_eq_fintype_card, ZMod.card, ← pow_mul, Nat.mul_comm, Nat.mul_left_comm]

/--
---
conclusion: Lax342547.KernelWitness.kernel_event_bound
---
Cover the large-kernel event by the zero-image events of all bounded
coefficient certificates. Each valid certificate satisfies the cap;
invalid ones contribute an empty event. Apply the finite union bound.
-/
theorem kernel_event_bound {Ω Comp I N : Type}
    [Fintype Ω] [Fintype Comp] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Comp → Matrix N I Binary) (q : ℕ) (cap : ℝ≥0∞)
    (hcap : ∀ C : Comp → Matrix I (Fin q) Binary, q ≤ (∑ e, (C e).rank) →
      p.toOuterMeasure {o | ∀ e, A o e * C e = 0} ≤ cap) :
    p.toOuterMeasure {o | q ≤ ∑ e, Module.finrank Binary (LinearMap.ker (A o e).mulVecLin)} ≤
      (2 : ℝ≥0∞) ^ (Fintype.card Comp * Fintype.card I * q) * cap := by
  classical
  let T := Comp → Matrix I (Fin q) Binary
  let S (C : T) : Set Ω := {o | q ≤ (∑ e, (C e).rank) ∧ ∀ e, A o e * C e = 0}
  have hcover : {o | q ≤ ∑ e, Module.finrank Binary (LinearMap.ker (A o e).mulVecLin)} ⊆ ⋃ C : T, S C := by
    intro o ho
    obtain ⟨C, hC, hrank⟩ := Lax342547.KernelWitness.exists_family_witness (A o) q ho
    exact Set.mem_iUnion.mpr ⟨C, hrank, hC⟩
  have hb (C : T) : p.toOuterMeasure (S C) ≤ cap := by
    by_cases hrank : q ≤ ∑ e, (C e).rank
    · exact (p.toOuterMeasure.mono (fun _ h => h.2)).trans (hcap C hrank)
    · have he : S C = ∅ := by ext o; simp [S, hrank]
      simp [he]
  calc
    _ ≤ p.toOuterMeasure (⋃ C : T, S C) := p.toOuterMeasure.mono hcover
    _ ≤ ∑ C : T, p.toOuterMeasure (S C) := MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _C : T, cap := Finset.sum_le_sum (fun C _ => hb C)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
      change (Nat.card (Comp → Matrix I (Fin q) Binary) : ℝ≥0∞) * cap = _
      rw [Lax342547.KernelWitness.coefficient_count]
      simp

end Lax342547Proofs.KernelWitness
