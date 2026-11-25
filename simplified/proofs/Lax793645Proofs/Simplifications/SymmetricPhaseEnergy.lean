import Lax793645Proofs.Simplifications.SymmetricOffsetRecords
import Lax793645Proofs.Simplifications.ImageTupleBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I J : Type} [Fintype I] [Fintype J]

theorem matrix_pair_cross_left (M : Mat I I) (T Z : Mat I J) :
    mpair M (T*Zᵀ)=mpair Z (Mᵀ*T) := by
  rw [mpair_comm Z]
  change (M*(T*Zᵀ)ᵀ).trace=((Mᵀ*T)*Zᵀ).trace
  rw [transpose_mul,transpose_transpose,←trace_transpose ((Mᵀ*T)*Zᵀ),
    transpose_mul,transpose_mul,transpose_transpose,←Matrix.mul_assoc Z]
  simpa only [transpose_transpose] using (Matrix.trace_mul_comm M (Z*Tᵀ))

theorem matrix_pair_cross_right (M : Mat I I) (T Z : Mat I J) :
    mpair M (Z*Tᵀ)=mpair Z (M*T) := by
  rw [mpair_comm Z]
  change (M*(Z*Tᵀ)ᵀ).trace=((M*T)*Zᵀ).trace
  rw [transpose_mul,transpose_transpose,Matrix.mul_assoc]

theorem symmetric_cross_phase (M : Mat I I) (T Z : Mat I J) :
    mpair M (T*Zᵀ+Z*Tᵀ)=mpair Z ((M+Mᵀ)*T) := by
  rw [map_add,matrix_pair_cross_left,matrix_pair_cross_right,Matrix.add_mul,map_add,add_comm]

variable {p : Shape} {r N : ℕ} {S : SymCover p N}

def symmetricHeat (M : Ambient p N) (X : SymAtlas p r S) : SymBatch X N :=
  fun e=>(M e+(M e)ᵀ)*symSrc X e

/-- Polar values determine the mixed part, while the remaining
quadratic value on the cover must also be retained. -/
theorem symmetric_offset_phase (M : Ambient p N) (X : SymAtlas p r S) (Z : SymBatch X N) :
    (∑ e,mpair (M e) (symSpelled X Z e))=
      imageTuplePair (symBreadth X) N Z (symmetricHeat M X)+
        ∑ e,mpair (M e) (symEdgeCost X e) := by
  rw [image_tuple_pair_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  change mpair (M e) (symSrc X e*(Z e)ᵀ+Z e*(symSrc X e)ᵀ+symEdgeCost X e)=_
  rw [map_add,symmetric_cross_phase]
  rfl

theorem phase_action_matrix {A H D : Type} [Fintype A] [Fintype H] [Fintype D]
    [DecidableEq A] [DecidableEq H] [DecidableEq D]
    (X Y : Mat A H) (T : Mat A D) :
    (Y*Xᵀ+(Y*Xᵀ)ᵀ)*T=quadraticPhaseAction X T Y := by
  rw [transpose_mul,transpose_transpose,Matrix.add_mul]
  simp only [Matrix.mul_assoc,quadraticPhaseAction,LinearMap.coe_mk,AddHom.coe_mk]

end
end Lax793645Proofs.Simplifications
