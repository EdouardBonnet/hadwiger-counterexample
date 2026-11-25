import Lax793645Proofs.Simplifications.QuadraticGramKernelBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

def quadraticPairGood (M : Mat I I) (z : Mat (Fin N) I×Mat (Fin N) I) : Prop:=
  Injective (stackMatrixEquiv N z).mulVec  ∧ quadraticPairCode z=quadraticGramCode M

theorem quadratic_stack_form (z : Mat (Fin N) I×Mat (Fin N) I) :
    (hyperbolicMatrix N).toQuadraticForm'.comp (stackFrameEquiv N z)=
      (z.1ᵀ*z.2).toQuadraticForm' := by
  apply QuadraticMap.ext
  intro x
  change (hyperbolicMatrix N).toQuadraticForm' (stackFrameEquiv N z x)=
    (z.1ᵀ*z.2).toQuadraticForm' x
  rw [hyperbolic_matrix_apply,stack_frame_apply,hyperbolic_apply]
  change dotProduct (z.1*ᵥx) (z.2*ᵥx)=Matrix.toBilin' (z.1ᵀ*z.2) x x
  rw [Matrix.toBilin'_apply',←Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec,dotProduct_comm]

theorem quadratic_pair_good_frame (M : Mat I I) (z : Mat (Fin N) I×Mat (Fin N) I) :
    quadraticPairGood M z  ↔ quadraticGramGood (hyperbolicMatrix N).toQuadraticForm'
      M.toQuadraticForm' (stackFrameEquiv N z) := by
  change (Injective (stackMatrixEquiv N z).mulVec  ∧ 
    quadraticGramCode (z.1ᵀ*z.2)=quadraticGramCode M)  ↔ _
  rw [quadratic_gram_code_eq]
  change _  ↔ Injective (stackFrameEquiv N z)  ∧ _
  rw [quadratic_stack_form]
  rfl

theorem quadratic_pair_good_lower (M : Mat I I) (hN : 2*num I+2 ≤ N) :
    unif (quadraticGramCode M)/4 ≤ 
      pr (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I)) (quadraticPairGood M) := by
  letI : Fintype (Vec I →ₗ[F] Vec (HyperbolicIdx N)):=
    Fintype.ofInjective (fun f=>⇑f) DFunLike.coe_injective
  have hh:=quadratic_gram_code_lower N M hN
  rw [←probability_equiv (stackFrameEquiv (I:=I) N),pair_unif] at hh
  simpa only [←quadratic_pair_good_frame] using hh

theorem quadratic_pair_good_pos (M : Mat I I) (hN : 2*num I+2 ≤ N) :
    0<pr (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I)) (quadraticPairGood M) := by
  have hu : 0<unif (quadraticGramCode M):=by rw [unif_apply]; positivity
  exact (div_pos hu (by norm_num)).trans_le (quadratic_pair_good_lower M hN)

theorem quadratic_pair_code_pos (M : Mat I I) (hN : 2*num I+2 ≤ N) :
    0<pr (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I))
      (fun z=>quadraticPairCode z=quadraticGramCode M) :=
  (quadratic_pair_good_pos M hN).trans_le
    (pr_mono (pairW_law unif_law unif_law).nz (fun _ h=>h.2))

theorem quadratic_conditioned_injective_mass (M : Mat I I) (hN : 2*num I+2 ≤ N) :
    (1:ℝ)/8 ≤ pr (onW (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I))
      (fun z=>quadraticPairCode z=quadraticGramCode M))
      (fun z=>Injective (stackMatrixEquiv N z).mulVec) := by
  rw [pr_on]
  apply (le_div_iff₀ (quadratic_pair_code_pos M hN)).mpr
  have hl:=quadratic_pair_good_lower M hN
  have hu:=quadratic_gram_code_upper N (quadraticGramCode M) hN
  have he : (fun z : Mat (Fin N) I×Mat (Fin N) I=>
      quadraticPairCode z=quadraticGramCode M  ∧ Injective (stackMatrixEquiv N z).mulVec)=
      quadraticPairGood M := by funext z; exact propext and_comm
  rw [he]
  linarith only [hl,hu]

end
end Lax793645Proofs.Simplifications
