import Lax793645Proofs.Simplifications.LinearTestRefinement
import Mathlib.Logic.Equiv.Fin.Basic

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A B C I : Type} [Fintype A] [Fintype B] [Fintype C]
  [Fintype I] [DecidableEq I]

theorem banner_equivalence (μ f : Wgt A) (P : A→B) (E : B≃C) :
    banner μ (E∘P) f=banner μ P f := by
  funext x
  unfold banner cashbook
  simp only [Function.comp_apply,←map_nested,mapW_equiv_val,Equiv.symm_apply_apply]

theorem append_mul_vec {r s : ℕ} (P : Mat (Fin r) I) (R : Mat (Fin s) I) (x : Vec I) :
    (Fin.append P R)*ᵥx=(Fin.appendEquiv r s) (P*ᵥx,R*ᵥx) := by
  funext j
  refine Fin.addCases (fun i=>?_) (fun i=>?_) j <;>
    simp [Matrix.mulVec,Fin.appendEquiv]

theorem banner_append {r s : ℕ} (μ f : Wgt (Vec I))
    (P : Mat (Fin r) I) (R : Mat (Fin s) I) :
    banner μ (Matrix.mulVec (Fin.append P R)) f=banner μ (fun x=>(P*ᵥx,R*ᵥx)) f := by
  have he : Matrix.mulVec (Fin.append P R)=(Fin.appendEquiv r s)∘(fun x=>(P*ᵥx,R*ᵥx)):=
    funext (append_mul_vec P R)
  rw [he,banner_equivalence]

theorem append_refines {r s : ℕ} (P : Mat (Fin r) I) (R : Mat (Fin s) I) :
    (fun x : Vec (Fin (r+s))=>fun i : Fin r=>x (i.castAdd s))∘Matrix.mulVec (Fin.append P R)=P.mulVec := by
  funext x i
  simp [Function.comp_apply,append_mul_vec,Fin.appendEquiv]

end
end Lax793645Proofs.Simplifications
