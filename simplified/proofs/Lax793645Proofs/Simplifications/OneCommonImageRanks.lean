import Lax793645Proofs.Simplifications.ImageKernelTails
import Lax793645Proofs.Simplifications.OneSymmetricOffsets
import Lax793645Proofs.Simplifications.OneRawImageCalendar

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap Submodule
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneFullImage (x : OneUnit p n N) (i : Bool) (e : Comp p.g) :
    OneFull p n→ₗ[F]Vec (Fin (2*N)):=
  (oneAmbientCoordinates N).toLinearMap.comp (x i e)

theorem one_full_image_join (x : OneUnit p n N) (e : Comp p.g) :
    colSp (oneCoordinateImages x e)=
      LinearMap.range (oneFullImage x true e)⊔LinearMap.range (oneFullImage x false e) := by
  apply le_antisymm
  · rintro z ⟨v,rfl⟩
    rw [show v=∑ i,oneEndpointInjection i (oneEndpointProjection i v) from
      (one_endpoint_coordinate_sum v).symm,map_sum]
    simp only [Matrix.mulVecLin_apply,one_endpoint_images,Fintype.sum_bool]
    exact add_mem_sup ⟨oneEndpointProjection true v,rfl⟩ ⟨oneEndpointProjection false v,rfl⟩
  · apply sup_le
    · rintro z ⟨v,rfl⟩
      exact ⟨oneEndpointInjection true v,one_endpoint_images x e true v⟩
    · rintro z ⟨v,rfl⟩
      exact ⟨oneEndpointInjection false v,one_endpoint_images x e false v⟩

theorem one_full_intersection_kernel (x : OneUnit p n N) (m : Mixer p n)
    (hx : ∀ i,oneFrameLaw m (x i)) (e : Comp p.g) :
    dim ↥(LinearMap.range (oneFullImage x true e)⊓LinearMap.range (oneFullImage x false e))=
      dim (oneCoordinateImages x e).mulVecLin.ker := by
  have h:=finrank_sup_add_finrank_inf_eq
    (LinearMap.range (oneFullImage x true e)) (LinearMap.range (oneFullImage x false e))
  have h' := (oneCoordinateImages x e).mulVecLin.finrank_range_add_finrank_ker
  rw [←one_full_image_join] at h
  have he i : dim (LinearMap.range (oneFullImage x i e))=dim (OneFull p n):=
    LinearMap.finrank_range_of_inj ((oneAmbientCoordinates N).injective.comp (hx i e).1)
  have hd : dim (Vec (OneColumn p n))=2*dim (OneFull p n) := by
    unfold dim
    rw [(oneEndpointCoordinates p n).finrank_eq,Module.finrank_pi_fintype]
    simp
  change dim (colSp (oneCoordinateImages x e))+
    dim ↥(LinearMap.range (oneFullImage x true e)⊓LinearMap.range (oneFullImage x false e))=
    dim (LinearMap.range (oneFullImage x true e))+dim (LinearMap.range (oneFullImage x false e)) at h
  change dim (colSp (oneCoordinateImages x e))+_=dim (Vec (OneColumn p n)) at h'
  rw [he,he] at h
  simp only [dim] at hd h h' ⊢
  omega

theorem one_dual_kernel_eq (x : OneUnit p n N) (e : Comp p.g) :
    (oneDualImages x e).mulVecLin.ker=(oneCoordinateImages x e).mulVecLin.ker := by
  ext v
  change oneDualImages x e*ᵥv=0 ↔ oneCoordinateImages x e*ᵥv=0
  rw [oneDualImages,←Matrix.mulVec_mulVec,LinearMap.toMatrix'_mulVec]
  exact (oneDuality N).map_eq_zero_iff

def oneJoins (x : OneUnit p n N) : ℕ:=imageKernelRank oneDualImages x

theorem one_primal_columns_full (x : OneUnit p n N) (i : Bool) (e : Comp p.g) :
    colSp (onePrimalMatrix (x i e)) ≤ LinearMap.range (oneFullImage x i e) := by
  rintro y ⟨v,rfl⟩
  refine ⟨(v,0),?_⟩
  rw [Matrix.mulVecLin_apply,onePrimalMatrix,LinearMap.toMatrix'_mulVec]
  rfl

theorem one_image_rank_exact (x : OneUnit p n N) (m : Mixer p n)
    (hx : ∀ i,oneFrameLaw m (x i)) (i : Bool) (z : Profile p n) (e : Comp p.g) :
    (oneImageProfile (x i) z e).rank=(z e).rank := by
  have hi : Injective (onePrimalMatrix (x i e)).mulVec := by
    intro u v he
    simp only [onePrimalMatrix,LinearMap.toMatrix'_mulVec,LinearMap.comp_apply,
      LinearEquiv.coe_coe] at he
    exact one_primal_injective (hx i) e ((oneAmbientCoordinates N).injective he)
  exact rank_lift_eq hi hi _

/-- A common quadratic moment image has the same rank on both sides.
Its total rank is bounded by the kernel of the joined physical frames. -/
theorem one_total_rank_shared (x : OneUnit p n N) (m : Mixer p n)
    (hx : ∀ i,oneFrameLaw m (x i)) {v w : Profile p n}
    (h : oneMomentEmbed (x true) v=oneMomentEmbed (x false) w) :
    totalRank v=totalRank w ∧ totalRank v ≤ oneJoins x := by
  have he : oneImageProfile (x true) v=oneImageProfile (x false) w := by
    rw [one_image_profile_readout,one_image_profile_readout,h]
  have hr e : (v e).rank=(w e).rank := by
    rw [←one_image_rank_exact x m hx true v e,he,one_image_rank_exact x m hx false w e]
  refine ⟨Finset.sum_congr rfl (fun e _=>hr e),Finset.sum_le_sum (fun e _=>?_)⟩
  have hcols : colSp (oneImageProfile (x true) v e) ≤
      LinearMap.range (oneFullImage x true e)⊓LinearMap.range (oneFullImage x false e) := by
    apply le_inf
    · exact (colSp_lift_le ..).trans (one_primal_columns_full x true e)
    · rw [he]
      exact (colSp_lift_le ..).trans (one_primal_columns_full x false e)
  change (v e).rank ≤ dim (oneDualImages x e).mulVecLin.ker
  rw [one_dual_kernel_eq,←one_full_intersection_kernel x m hx e,
    ←one_image_rank_exact x m hx true v e,←colSp_dim]
  exact Submodule.finrank_mono hcols

end
end Lax793645Proofs.Simplifications
