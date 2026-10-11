import Lax342547.SlotWalsh
import Lax342547.BilinearWalsh

namespace Lax342547Proofs.SlotWalsh

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.SlotWalsh

variable {I J : Type} [Fintype I] [Fintype J]

omit [Fintype I] in
theorem bit_mulVec (C : Matrix I J Binary) (N : ℕ) (v : Fin N × J → Binary)
    (a : Fin N) (i : I) :
    (bitMatrix C N).mulVec v (a, i) = C.mulVec (fun j => v (a, j)) i := by
  classical
  simp [Matrix.mulVec, dotProduct, bitMatrix, Fintype.sum_prod_type, ite_mul]

/--
---
conclusion: Lax342547.SlotWalsh.bit_evaluation
---
The bit matrix pairs equal bit coordinates. Interchanging the finite
sums gives the specified linear combination of the vector-slot dot products.
-/
theorem bit_evaluation (C : Matrix I J Binary) (N : ℕ)
    (x : Fin N × I → Binary) (y : Fin N × J → Binary) :
    dotProduct x ((bitMatrix C N).mulVec y) = ∑ i, ∑ j, C i j * ∑ a, x (a, i) * y (a, j) := by
  change (∑ z : Fin N × I, x z * (bitMatrix C N).mulVec y z) = _
  rw [Fintype.sum_prod_type]
  simp_rw [bit_mulVec]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

noncomputable def bitRangeEquiv (C : Matrix I J Binary) (N : ℕ) :
    LinearMap.range (bitMatrix C N).mulVecLin ≃ₗ[Binary] (Fin N → LinearMap.range C.mulVecLin) where
  toFun v a := ⟨fun i => v.val (a, i), by
    obtain ⟨w, hw⟩ := v.property
    refine ⟨fun j => w (a, j), ?_⟩
    funext i
    have h := congrFun hw (a, i)
    simpa only [Matrix.mulVecLin_apply, bit_mulVec] using h⟩
  invFun v := ⟨fun ai => (v ai.1).val ai.2, by
    choose w hw using fun a => (v a).property
    refine ⟨fun aj => w aj.1 aj.2, ?_⟩
    funext ⟨a, i⟩
    simp only [Matrix.mulVecLin_apply, bit_mulVec]
    exact congrFun (hw a) i⟩
  left_inv v := by apply Subtype.ext; rfl
  right_inv v := by funext a; apply Subtype.ext; rfl
  map_add' v w := rfl
  map_smul' c v := rfl

omit [Fintype I] in
/--
---
conclusion: Lax342547.SlotWalsh.bit_rank
---
The image of the bit matrix is linearly equivalent to N independent
copies of the coefficient matrix's image. Dimensions add over that
finite product, giving the exact bit rank.
-/
theorem bit_rank (C : Matrix I J Binary) (N : ℕ) : (bitMatrix C N).rank = N * C.rank := by
  change Module.finrank Binary (LinearMap.range (bitMatrix C N).mulVecLin) = _
  rw [(bitRangeEquiv C N).finrank_eq, Module.finrank_pi_fintype]
  simp [Matrix.rank]

omit [Fintype I] in
theorem rank_pos_of_ne_zero (C : Matrix I J Binary) (hC : C ≠ 0) : 0 < C.rank := by
  classical
  by_contra h
  have hz : Module.finrank Binary (LinearMap.range C.mulVecLin) = 0 := Nat.eq_zero_of_not_pos h
  have hbot : LinearMap.range C.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hz
  have hzero : C.mulVecLin = 0 := LinearMap.range_eq_bot.mp hbot
  apply hC
  ext i j
  have hj := congrFun (congrArg (fun f : (J → Binary) →ₗ[Binary] (I → Binary) =>
    f (Pi.single j 1)) hzero) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using hj

/--
---
conclusion: Lax342547.SlotWalsh.nonzero_pattern_bound
---
A nonzero coefficient matrix has rank at least one, so the full bit
form has rank at least N. The general bilinear Walsh estimate gives the
required correlation bound, uniformly in the two bounded group weights.
-/
theorem nonzero_pattern_bound [DecidableEq I] [DecidableEq J]
    (C : Matrix I J Binary) (hC : C ≠ 0) (N : ℕ)
    (f : (Fin N × I → Binary) → ℝ) (g : (Fin N × J → Binary) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    |Lax342547.BilinearWalsh.average (bitMatrix C N) f g| ≤ 1 / Real.sqrt ((2 : ℝ) ^ N) := by
  have h := Lax342547.BilinearWalsh.uniform_bound (bitMatrix C N) f g hf hg
  rw [Lax342547.SlotWalsh.bit_rank] at h
  refine h.trans ?_
  have hr : N ≤ N * C.rank := Nat.le_mul_of_pos_right N (rank_pos_of_ne_zero C hC)
  gcongr
  norm_num

end Lax342547Proofs.SlotWalsh
