import Lax793645Proofs.Simplifications.QuadraticGramKernelBounds
import Lax793645Proofs.Simplifications.InjectivityPolynomial

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

/-- A full-frame kernel tail under the quadratic Gram law. Half-frame
dependencies are retained and only used to bound this tail from above. -/
theorem quadratic_conditioned_deficiency (c : QuadraticGramCode I)
    (hN : 2*num I+2 ≤ N) (d : ℕ) :
    pr (onW (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I))
      (fun x=>quadraticPairCode x=c))
      (fun x=>d ≤ Fintype.card I-(stackMatrixEquiv N x).rank) ≤ 
        8*(d+1)*bp ((d:ℝ)*(4*num I-N)) := by
  have hroom : num I+num I-num (Fin N) ≤ -1 := by
    simp only [num,Fintype.card_fin] at *
    linarith
  apply conditional_coarsening_bound _ (pairW_law unif_law unif_law).nz
    (fun x=>x.1ᵀ*x.2) quadraticGramCode _ _
    (mul_nonneg (by positivity) (bp_pos _).le) _ c
  intro G
  have hmono (x : Mat (Fin N) I×Mat (Fin N) I)
      (hx : d ≤ Fintype.card I-(stackMatrixEquiv N x).rank) :
      d ≤ (Fintype.card I-x.1.rank)+(Fintype.card I-x.2.rank) := by
    have hr : x.1.rank ≤ (stackMatrixEquiv N x).rank:=
      (stackMatrixEquiv N x).rank_submatrix_le Sum.inl _root_.id
    omega
  refine (pr_mono (normW_nonneg
    (subW_nonneg (pairW_law unif_law unif_law).nz _)) hmono).trans ?_
  convert gram_conditioned_kernel_tail (U:=Fin N) G hroom d using 1 <;>
    norm_num only [num,Fintype.card_fin] <;> congr 2 <;> ring

def quadraticKernelSieve (d : ℕ) (x : Mat (Fin N) I×Mat (Fin N) I) : ℝ:=
  kernelSieve d (binaryKernelCount (stackMatrixEquiv N x))

def singleKernelSieveCost (I : Type) [Fintype I] (d : ℕ) : ℝ:=(2+bp (num I))^d

theorem quadratic_kernel_sieve_bound (d : ℕ) (x : Mat (Fin N) I×Mat (Fin N) I) :
    |quadraticKernelSieve d x| ≤ singleKernelSieveCost I d :=
  kernel_sieve_bound d _ _ (binary_kernel_count_bounds _).1 (binary_kernel_count_bounds _).2

theorem quadratic_kernel_sieve_exact (d : ℕ) (x : Mat (Fin N) I×Mat (Fin N) I)
    (hd : Fintype.card I-(stackMatrixEquiv N x).rank ≤ d) :
    quadraticKernelSieve d x=ind (Injective (stackMatrixEquiv N x).mulVec) :=
  matrix_sieve_exact _ d hd

/-- The exact physical-frame injectivity test has a finite polynomial
replacement. Its error is charged under the quadratic Gram law before
any capped leaf is introduced. -/
theorem quadratic_sieve_error (c : QuadraticGramCode I) (hN : 2*num I+2 ≤ N)
    (f : Wgt (Mat (Fin N) I×Mat (Fin N) I)) (hf : ∀ x,|f x| ≤ 1) (d : ℕ) :
    |avg (onW (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I))
      (fun x=>quadraticPairCode x=c))
      (fun x=>f x*(ind (Injective (stackMatrixEquiv N x).mulVec)-quadraticKernelSieve d x))| ≤ 
      (singleKernelSieveCost I d+1)*(8*(d+2)*bp (((d:ℝ)+1)*(4*num I-N))) := by
  let W:=onW (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I))
    (fun x=>quadraticPairCode x=c)
  let bad (x : Mat (Fin N) I×Mat (Fin N) I):=d+1 ≤ Fintype.card I-(stackMatrixEquiv N x).rank
  have hW : ∀ x,0 ≤ W x:=normW_nonneg (subW_nonneg (pairW_law unif_law unif_law).nz _)
  have hcost : 0 ≤ singleKernelSieveCost I d:=pow_nonneg (by linarith [bp_pos (num I)]) _
  have hpoint x :
      |f x*(ind (Injective (stackMatrixEquiv N x).mulVec)-quadraticKernelSieve d x)| ≤ 
        (singleKernelSieveCost I d+1)*ind (bad x) := by
    by_cases hx : bad x
    · rw [ind_one hx,mul_one,abs_mul]
      refine (mul_le_mul_of_nonneg_right (hf x) (abs_nonneg _)).trans ?_
      rw [one_mul]
      have hi : |ind (Injective (stackMatrixEquiv N x).mulVec)| ≤ 1 := by
        rw [abs_of_nonneg (ind_nonneg _)]
        exact ind_le_one _
      exact (abs_sub _ _).trans (by linarith [quadratic_kernel_sieve_bound d x])
    · have hd : Fintype.card I-(stackMatrixEquiv N x).rank ≤ d:=by dsimp [bad] at hx; omega
      rw [quadratic_kernel_sieve_exact d x hd,sub_self,mul_zero,abs_zero,ind_zero hx,mul_zero]
  refine ((abs_avg_le hW).trans (avg_mono hW hpoint)).trans ?_
  rw [avg_mul']
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ singleKernelSieveCost I d+1)
  change pr W bad ≤ _
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
    quadratic_conditioned_deficiency c hN (d+1)

theorem single_kernel_sieve_exponential (d : ℕ) :
    singleKernelSieveCost I d ≤ bp ((num I+2)*d) := by
  rw [bp_mul_nat]
  apply pow_le_pow_left₀ (by linarith [bp_pos (num I)])
  have h1 : 1 ≤ bp (num I) := by rw [←bp_zero]; exact bp_le (Nat.cast_nonneg _)
  have hb2 : bp 2=4 := by rw [show (2:ℝ)=1+1 by norm_num,bp_add,bp_one]; norm_num
  rw [bp_add,hb2]
  linarith

end
end Lax793645Proofs.Simplifications
