import Lax342547.BilinearMean
import Lax342547Proofs.BilinearWalsh

namespace Lax342547Proofs.BilinearMean
open Lax342547.BilinearMean

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh
open scoped BigOperators

/--
---
conclusion: Lax342547.BilinearMean.bilinear_character_average
---
-/
theorem bilinear_character_average {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (A : Matrix I J Binary) :
    (∑ x : I → Binary, ∑ y : J → Binary, phase x (A.mulVec y))/
      ((2 : ℝ)^Fintype.card I*2^Fintype.card J) = 1/(2 : ℝ)^A.rank := by
  classical
  have hsum : (∑ x : I → Binary, ∑ y : J → Binary, phase x (A.mulVec y)) =
      (2 : ℝ)^Fintype.card I*((Finset.univ.filter (fun y : J → Binary => A.mulVec y = 0)).card : ℝ) := by
    rw [Finset.sum_comm]
    have hf (y : J → Binary) : (∑ x : I → Binary, phase x (A.mulVec y)) =
        if A.mulVec y = 0 then (2 : ℝ)^Fintype.card I else 0 := by
      simpa only [Lax342547Proofs.Walsh.phase_comm] using Lax342547Proofs.Walsh.sum_phase (A.mulVec y)
    simp_rw [hf]
    rw [Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  have hker : (Finset.univ.filter (fun y : J → Binary => A.mulVec y = 0)).card =
      Fintype.card (LinearMap.ker A.mulVecLin) := by
    simp only [Fintype.card_subtype,LinearMap.mem_ker,Matrix.mulVecLin_apply]
  have hd := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hd
  have hk : Module.finrank Binary (LinearMap.ker A.mulVecLin) = Fintype.card J-A.rank := by
    change A.rank+Module.finrank Binary (LinearMap.ker A.mulVecLin) = Fintype.card J at hd
    omega
  rw [hsum,hker,Lax342547Proofs.FiniteLinearLaw.binary_card (LinearMap.ker A.mulVecLin),hk]
  push_cast
  have hr := Matrix.rank_le_card_width A
  have he : (2 : ℝ)^(Fintype.card J-A.rank)*2^A.rank = 2^Fintype.card J := by
    rw [← pow_add,Nat.sub_add_cancel hr]
  have hp : (2 : ℝ)^Fintype.card J ≠ 0 := by positivity
  have hpi : (2 : ℝ)^Fintype.card I ≠ 0 := by positivity
  have hpr : (2 : ℝ)^A.rank ≠ 0 := by positivity
  field_simp
  nlinarith

end Lax342547Proofs.BilinearMean
