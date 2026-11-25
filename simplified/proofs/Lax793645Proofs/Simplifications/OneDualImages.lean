import Lax793645Proofs.Simplifications.OneImagePinCaps
import Lax793645Proofs.Simplifications.OneChannelCoordinates
import Lax793645Proofs.Simplifications.ImageSeparatedObservations

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def oneDuality (N : ℕ) : Vec (Fin (2*N))≃ₗ[F]Vec (Fin (2*N)):=
  (oneAmbientCoordinates N).symm.trans (oneDualCoordinates N)

def oneDualImages (x : OneUnit p n N) (e : Comp p.g) : Mat (Fin (2*N)) (OneColumn p n):=
  LinearMap.toMatrix' (oneDuality N).toLinearMap*oneCoordinateImages x e

theorem one_dual_images_apply (x : OneUnit p n N) (e : Comp p.g) (v : Vec (OneColumn p n)) :
    oneDualImages x e*ᵥv=oneDualCoordinates N (oneUnitMap x e (oneNominalCoordinates p n v)) := by
  rw [oneDualImages,←mulVec_mulVec,LinearMap.toMatrix'_mulVec,one_coordinate_images_apply]
  simp only [oneDuality,LinearEquiv.trans_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

theorem one_dual_endpoint_images (x : OneUnit p n N) (e : Comp p.g) (i : Bool) (v : OneFull p n) :
    oneDualImages x e*ᵥoneEndpointInjection i v=oneDualCoordinates N (x i e v) := by
  rw [oneDualImages,←mulVec_mulVec,LinearMap.toMatrix'_mulVec,one_endpoint_images]
  simp only [oneDuality,LinearEquiv.trans_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]

/-- Polar coordinates preserve every raw pin bound. This allows the
primal companions and quadratic polar actions to share one image count. -/
theorem one_dual_image_pin_cap (m : Mixer p n)
    (a : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    {ζ : ℝ} (hz : 0≤ζ) (hz' : ζ≤6)
    (hN : 2*dim (OneFull p n)+3≤N)
    (hζ : (dim (OneFull p n):ℝ)+2≤(ζ/6)*(2*N)) :
    pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ζ (imagePlanRank a.sp) := by
  classical
  have hw : ∀ x,0≤oneUnitRaw m N x:=prodW_nonneg (fun _=>one_raw_nonneg m)
  by_cases hp : 0<pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)
  · obtain ⟨x,hx,_⟩:=exists_of_pr_pos hw hp
    let b : ImagePin (Comp p.g) (OneColumn p n) (2*N):=⟨a.sp,oneCoordinateImages x⟩
    apply (pr_mono hw (q:=imagePinAgree oneCoordinateImages b) ?_).trans
      (one_image_pin_cap m b hz hz' hN hζ)
    intro y hy e v hv
    apply (oneDuality N).injective
    have he:=(hy e v hv).trans (hx e v hv).symm
    simpa only [oneDualImages,←mulVec_mulVec,LinearMap.toMatrix'_mulVec,LinearEquiv.coe_coe] using he
  exact (not_lt.mp hp).trans (bp_pos _).le

end
end Lax793645Proofs.Simplifications
