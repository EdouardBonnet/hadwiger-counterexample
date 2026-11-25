import Lax793645Proofs.Simplifications.HyperbolicCoordinates
import Lax793645Proofs.Simplifications.QuadraticOrbitLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.GramProbabilities
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalProductLaws
import Mathlib.Data.Matrix.ColumnRowPartitioned

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I]

def stackMatrixEquiv (N : ℕ) :
    (Mat (Fin N) I×Mat (Fin N) I)≃Mat (HyperbolicIdx N) I where
  toFun P:=Matrix.fromRows P.1 P.2
  invFun M:=(M.submatrix Sum.inl id,M.submatrix Sum.inr id)
  left_inv P:=rfl
  right_inv M:=by ext i j; cases i <;> rfl

def stackFrameEquiv (N : ℕ) :
    (Mat (Fin N) I×Mat (Fin N) I)≃(Vec I→ₗ[F]Vec (HyperbolicIdx N)) :=
  (stackMatrixEquiv N).trans Matrix.toLin'.toEquiv

theorem stack_frame_apply (N : ℕ) (P : Mat (Fin N) I×Mat (Fin N) I) (x : Vec I) :
    stackFrameEquiv N P x=Sum.elim (P.1*ᵥx) (P.2*ᵥx) := by
  change (Matrix.fromRows P.1 P.2)*ᵥx=_
  exact Matrix.fromRows_mulVec _ _ _

theorem paired_gram_quadratic (N : ℕ) (M : Mat I I)
    (P : Mat (Fin N) I×Mat (Fin N) I) (hP : gramGood M P) :
    quadraticGramGood (hyperbolicMatrix N).toQuadraticForm'
      M.toQuadraticForm' (stackFrameEquiv N P) := by
  refine ⟨?_,?_⟩
  · intro x y he
    apply hP.2.1
    exact congrArg (fun f : Vec (HyperbolicIdx N)=>f∘Sum.inl)
      ((stack_frame_apply N P x).symm.trans (he.trans (stack_frame_apply N P y)))
  · apply QuadraticMap.ext
    intro x
    change (hyperbolicMatrix N).toQuadraticForm' (stackFrameEquiv N P x)=M.toQuadraticForm' x
    rw [hyperbolic_matrix_apply,stack_frame_apply,hyperbolic_apply]
    change dotProduct (P.1*ᵥx) (P.2*ᵥx)=Matrix.toBilin' M x x
    rw [Matrix.toBilin'_apply',←hP.1,←Matrix.mulVec_mulVec,
      Matrix.dotProduct_transpose_mulVec,dotProduct_comm]

theorem probability_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A≃B) (p : B→Prop) : pr unif (fun x=>p (e x))=pr unif p := by
  unfold pr avg
  simp only [unif_apply,Fintype.card_congr e]
  exact Equiv.sum_comp e (fun x : B=>(Fintype.card B:ℝ)⁻¹*ind (p x))

/-- A useful lower normalization bound needs only a subset of the quadratic
frames. Stacking an ordinary prescribed-Gram pair supplies that subset. -/
theorem quadratic_gram_lower (N : ℕ)
    [Fintype (Vec I→ₗ[F]Vec (HyperbolicIdx N))] (M : Mat I I)
    (hN : 2*num I+2≤N) :
    bp (-(num I)^2-2)≤pr unif (quadraticGramGood
      (hyperbolicMatrix N).toQuadraticForm' M.toQuadraticForm') := by
  have hsize : num I+num I≤num (Fin N) := by
    simp only [num,Fintype.card_fin] at *
    linarith
  have hg:=(gram_norm (U:=Fin N) M hsize).2
  have hn : 0≤num I:=by unfold num; positivity
  have hsmall : bp (num I-num (Fin N))≤(1/2:ℝ) := by
    calc
      _ ≤ bp (-1) := bp_le (by simp only [num,Fintype.card_fin] at *; linarith)
      _ = _ := by norm_num [bp]
  have hlarge : bp (num I+num I-num (Fin N))≤(1/2:ℝ) := by
    calc
      _ ≤ bp (-1) := bp_le (by simp only [num,Fintype.card_fin] at *; linarith)
      _ = _ := by norm_num [bp]
  have hlo : bp (-num I*num I)/4≤
      bp (-num I*num I)*(1-bp (num I-num (Fin N)))*
        (1-bp (num I+num I-num (Fin N))) := by
    have hb:=bp_pos (-num I*num I)
    have hp : (1/2:ℝ)*(1/2)≤(1-bp (num I-num (Fin N)))*
        (1-bp (num I+num I-num (Fin N))) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hp hb.le]
  have he : bp (-(num I)^2-2)=bp (-num I*num I)/4 := by
    rw [bp_sub]
    rw [show -(num I)^2= -num I*num I by ring]
    norm_num [bp]
  rw [he]
  refine (hlo.trans hg).trans ?_
  rw [←pair_unif,←probability_equiv (stackFrameEquiv (I:=I) N)]
  exact pr_mono unif_subLaw.nz (paired_gram_quadratic N M)

end
end Lax793645Proofs.Simplifications
