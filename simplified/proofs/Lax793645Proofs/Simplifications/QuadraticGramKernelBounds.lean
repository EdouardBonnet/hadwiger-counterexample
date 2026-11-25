import Lax793645Proofs.Simplifications.QuadraticGramNormalization
import Lax793645Proofs.Simplifications.GramKernelBounds
import Lax793645Proofs.Simplifications.ConditionalCoarsening

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

def quadraticPairCode {N : ℕ} (x : Mat (Fin N) I×Mat (Fin N) I) : QuadraticGramCode I:=
  quadraticGramCode (x.1ᵀ*x.2)

/-- A quadratic Gram fiber has probability at most twice its uniform code
mass. Redundant ordered Gram equations do not enter the normalization. -/
theorem quadratic_gram_code_upper (N : ℕ) (c : QuadraticGramCode I)
    (hN : 2*num I+2≤N) :
    pr (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I))
      (fun x=>quadraticPairCode x=c)≤2*unif c := by
  let μ : Wgt (Mat (Fin N) I×Mat (Fin N) I):=pairW unif unif
  have hroom : num I+num I-num (Fin N)≤-1 := by
    simp only [num,Fintype.card_fin] at *
    linarith
  have hu (G : Mat I I) : mapW μ (fun x=>x.1ᵀ*x.2) G≤2*unif G := by
    have he : unif G=bp (-num I*num I) := by
      rw [unif_apply,card_space,dim_mat,←bp_neg]
      congr 1
      push_cast
      unfold num
      ring
    rw [he]
    exact gram_unrestricted_upper G hroom
  have hh:=mapW_cap hu quadraticGramCode c
  rw [quadratic_gram_code_uniform,mapW_nested] at hh
  exact hh

/-- Kernel bounds for the ordered Gram law pass to the quadratic law
without conditioning on one particular ordered table. -/
theorem quadratic_conditioned_kernel_bound {E : Type} [Fintype E] [DecidableEq E]
    (N : ℕ) (A : Mat I E) (hA : Injective A.mulVec)
    (c : QuadraticGramCode I) (hN : 2*num I+2≤N) :
    pr (onW (pairW unif unif : Wgt (Mat (Fin N) I×Mat (Fin N) I))
      (fun x=>quadraticPairCode x=c))
      (fun x=>x.1*A=0 ∧ x.2*A=0)≤8*bp (2*num E*(2*num I-N)) := by
  have hroom : num I+num I-num (Fin N)≤-1 := by
    simp only [num,Fintype.card_fin] at *
    linarith
  apply conditional_coarsening_bound _ (pairW_law unif_law unif_law).nz
    (fun x=>x.1ᵀ*x.2) quadraticGramCode _ _
      (mul_nonneg (by norm_num) (bp_pos _).le) _ c
  intro G
  convert gram_conditioned_kernel_bound A A hA hA G hroom using 1
  congr 2
  simp only [num,Fintype.card_fin]
  ring

/-- Both halves may be dependent. Only a kernel of the complete physical
frame is excluded by the one-frame construction. -/
theorem quadratic_stack_kernel (N : ℕ) {E : Type} [Fintype E]
    (x : Mat (Fin N) I×Mat (Fin N) I) (A : Mat I E) :
    stackMatrixEquiv N x*A=0 ↔x.1*A=0 ∧ x.2*A=0 := by
  change Matrix.fromRows x.1 x.2*A=0 ↔_
  rw [Matrix.fromRows_mul]
  constructor
  · intro h
    exact ⟨congrArg (fun M=>M.submatrix Sum.inl _root_.id) h,
      congrArg (fun M=>M.submatrix Sum.inr _root_.id) h⟩
  · rintro ⟨h₁,h₂⟩
    rw [h₁,h₂]
    ext i j
    cases i <;> rfl

end
end Lax793645Proofs.Simplifications
