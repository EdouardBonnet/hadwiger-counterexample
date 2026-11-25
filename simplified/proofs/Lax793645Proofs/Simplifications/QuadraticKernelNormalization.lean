import Lax793645Proofs.Simplifications.QuadraticPrescribedKernels

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I R : Type} [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R] {N : ℕ}

theorem quadratic_prescribed_lower (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R)
    (hN : 2*num R+2 ≤ N) :
    bp (2*(N:ℝ)*(num R-num I)-(dim (QuadraticGramCode R):ℝ))/4 ≤
      pr (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I)) (quadraticPrescribedKernel L Q) := by
  rw [quadratic_prescribed_mass L hL Q]
  have hh:=quadratic_pair_good_lower Q hN
  rw [unif_apply,card_space,←bp_neg] at hh
  have hm:=mul_le_mul_of_nonneg_left hh (bp_pos (2*(N:ℝ)*(num R-num I))).le
  rw [←mul_div_assoc,←bp_add] at hm
  simpa only [sub_eq_add_neg] using hm

theorem quadratic_prescribed_pos (L : Mat R I) (hL : Surjective L.mulVec) (Q : Mat R R)
    (hN : 2*num R+2 ≤ N) :
    0<pr (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I)) (quadraticPrescribedKernel L Q) :=
  (div_pos (bp_pos _) (by norm_num)).trans_le (quadratic_prescribed_lower L hL Q hN)

/-- The original quadratic expansion pays only the prescribed nominal
deficiency. No quadratic-in-batch-size normalization loss remains. -/
theorem quadratic_original_expansion_cost (L : Mat R I) (hL : Surjective L.mulVec)
    (Q : Mat R R) (hN : 2*num R+2 ≤ N) :
    bp (-(dim (QuadraticGramCode I):ℝ))/
      pr (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I)) (quadraticPrescribedKernel L Q) ≤
      4*bp (2*(N:ℝ)*(num I-num R)) := by
  have hd : (dim (QuadraticGramCode R):ℝ) ≤ dim (QuadraticGramCode I):=by
    exact_mod_cast quadratic_code_dimension_mono L hL
  refine (div_le_div₀ (bp_pos _).le le_rfl (div_pos (bp_pos _) (by norm_num))
    (quadratic_prescribed_lower L hL Q hN)).trans ?_
  calc
    _=4*bp (-(dim (QuadraticGramCode I):ℝ)-
      (2*(N:ℝ)*(num R-num I)-(dim (QuadraticGramCode R):ℝ))) := by
      have hc (x y : ℝ) : x/(y/4)=4*(x/y):=by ring
      rw [hc,←bp_sub]
    _ ≤ _:=mul_le_mul_of_nonneg_left (bp_le (by nlinarith only [hd])) (by norm_num)

end
end Lax793645Proofs.Simplifications
