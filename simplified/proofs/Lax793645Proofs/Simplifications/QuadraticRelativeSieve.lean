import Lax793645Proofs.Simplifications.QuadraticRelationLaws
import Lax793645Proofs.Simplifications.QuadraticKernelNormalization

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I R : Type} [Fintype I] [Fintype R] [DecidableEq I] [DecidableEq R] {N : ℕ}

/-- Only the prescribed kernel cardinality is divided out. The sieve
still acts on the original physical columns, including every relation. -/
def relativeQuadraticSieve (R : Type) [Fintype R] (d : ℕ) (z : Rack I N) : ℝ:=
  kernelSieve d (bp (num R-num I)*binaryKernelCount (stackMatrixEquiv N z))

theorem relative_quadratic_sieve_quotient (L : Mat R I) (hL : Surjective L.mulVec)
    (d : ℕ) (z : Rack R N) :
    relativeQuadraticSieve R d (z.1*L,z.2*L)=quadraticKernelSieve d z := by
  simp only [relativeQuadraticSieve,stack_matrix_quotient,scaled_kernel_count L hL,
    quadraticKernelSieve]

theorem relative_quadratic_sieve_fourier_norm {D : Type} [Fintype D] [DecidableEq D]
    (P : Vec D →ₗ[F] Mat (HyperbolicIdx N) I) (d : ℕ) :
    fourierNorm (fun x=>kernelSieve d
      (bp (num R-num I)*binaryKernelCount (P x))) ≤ singleKernelSieveCost R d := by
  have hP : fourierNorm (fun x=>bp (num R-num I)*binaryKernelCount (P x)) ≤ bp (num R) := by
    rw [fourier_norm_smul,abs_of_pos (bp_pos _)]
    exact (mul_le_mul_of_nonneg_left (fourier_norm_kernel_count P) (bp_pos _).le).trans_eq
      (by rw [←bp_add]; congr 1; ring)
  exact fourier_norm_sieve _ d _ hP

theorem quadratic_sieve_error_exponential (c : QuadraticGramCode I) (hN : 2*num I+2 ≤ N)
    (f : Wgt (Rack I N)) (hf : ∀ x,|f x| ≤ 1) (d : ℕ) :
    |avg (onW (pairW unif unif : Wgt (Rack I N)) (fun x=>quadraticPairCode x=c))
      (fun x=>f x*(ind (Injective (stackMatrixEquiv N x).mulVec)-quadraticKernelSieve d x))| ≤
      16*(d+2)*bp ((num I+2)*d+((d:ℝ)+1)*(4*num I-N)) := by
  have hb : 1 ≤ bp ((num I+2)*d) := by
    rw [←bp_zero]
    exact bp_le (mul_nonneg (by positivity) (Nat.cast_nonneg _))
  have hc : singleKernelSieveCost I d+1 ≤ 2*bp ((num I+2)*d) := by
    linarith [single_kernel_sieve_exponential (I:=I) d]
  refine (quadratic_sieve_error c hN f hf d).trans ?_
  calc
    _ ≤ (2*bp ((num I+2)*d))*(8*(d+2)*bp (((d:ℝ)+1)*(4*num I-N))) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) (bp_pos _).le)
    _ = _ := by rw [bp_add]; ring

/-- The additional image-kernel error is charged after dividing out the
nominal relations. No nominal-deficiency multiplier appears in it. -/
theorem quadratic_original_columns_sieve_error (L : Mat R I) (hL : Surjective L.mulVec)
    (Q : Mat R R) (hN : 2*num R+2 ≤ N)
    (f : Wgt (Rack I N)) (hf : ∀ z,|f z| ≤ 1) (d : ℕ) :
    |avg (unifOn (quadraticRelation (N:=N) L Q))
      (fun z=>f z*(ind ((stackMatrixEquiv N z).mulVecLin.ker=L.mulVecLin.ker)-
        relativeQuadraticSieve R d z))| ≤
      16*(d+2)*bp ((num R+2)*d+((d:ℝ)+1)*(4*num R-N)) := by
  rw [←quotient_quadratic_law L hL Q,mapW_avg]
  simp_rw [stack_matrix_quotient,exact_kernel_mul_iff L hL,
    relative_quadratic_sieve_quotient L hL]
  exact quadratic_sieve_error_exponential (quadraticGramCode Q) hN
    (fun z=>f (z.1*L,z.2*L)) (fun z=>hf _) d

end
end Lax793645Proofs.Simplifications
