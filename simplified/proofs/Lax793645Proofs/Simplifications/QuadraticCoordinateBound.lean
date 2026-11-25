import Lax793645Proofs.Simplifications.LinearCellCoordinates
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRankCounting

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Function Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V Q I : Type} [AddCommGroup V] [Module F V] [Fintype I] [DecidableEq I]

/-- Rank factorization bounds the number of coordinates of a fitted
quadratic, independently of the partition from which it was fitted. -/
theorem affine_matrix_linear_cells (M : Mat I I) (P : V→ₗ[F]Vec I)
    (k : Vec I) (c : F) (r : ℕ) (hr : M.rank≤r) :
    HasLinearCells (fun (_ : Q) x=>evmat M (P x+k) (P x+k)+c) (2*r) := by
  obtain ⟨A,B,hAB⟩:=mul_factor M r hr
  let L : Bool→V→ₗ[F]Vec (Fin r) := fun b=>
    if b then A.transpose.mulVecLin.comp P else B.mulVecLin.comp P
  have hL (b : Bool) : HasLinearCells (fun (_ : Q) x=>L b x) r :=
    ⟨r,le_rfl,L b,fun _ x=>x,fun _ _=>rfl⟩
  have h := linear_cells_bundle (fun _ : Bool=>r) (fun b (_ : Q) x=>L b x) hL
  have hs : (∑ _ : Bool,r)=2*r := by simp
  rw [hs] at h
  have hh:=linear_cells_postprocess h (fun (_ : Q) z=>
    dotProduct (z true+A.transpose*ᵥk) (z false+B*ᵥk)+c)
  convert hh using 1
  funext q x
  simp only [L,Bool.false_eq_true,if_true,if_false,LinearMap.comp_apply,
    Matrix.mulVecLin_apply,←Matrix.mulVec_add]
  rw [dotProduct_comm (A.transpose*ᵥ(P x+k)),←dotProduct_transpose_mulVec,
    Matrix.transpose_transpose,Matrix.mulVec_mulVec,hAB]
  rfl

end
end Lax793645Proofs.Simplifications
