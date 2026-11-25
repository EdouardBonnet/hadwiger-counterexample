import Lax793645Proofs.Simplifications.ImageGramHits
import Lax793645Proofs.Simplifications.OneClosedImagePartitions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

def oneAmbientPolar (N : ℕ) : LinearMap.BilinForm F (Vec (Fin (2*N))) :=
  (hyperbolicMatrix N).toQuadraticForm'.polarBilin.compl₁₂
    (oneAmbientCoordinates N).symm.toLinearMap (oneAmbientCoordinates N).symm.toLinearMap

def onePolarMatrix (N : ℕ) : Mat (Fin (2*N)) (Fin (2*N)):=
  LinearMap.toMatrix₂' F (oneAmbientPolar N)

theorem one_ambient_polar_nondegenerate (N : ℕ) : (oneAmbientPolar N).Nondegenerate := by
  constructor
  · intro v hv
    apply (oneAmbientCoordinates N).symm.injective
    rw [map_zero]
    apply (hyperbolic_matrix_nondegenerate N).1
    intro w
    have h:=hv (oneAmbientCoordinates N w)
    simpa only [oneAmbientPolar,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using h
  · intro v hv
    apply (oneAmbientCoordinates N).symm.injective
    rw [map_zero]
    apply (hyperbolic_matrix_nondegenerate N).2
    intro w
    have h:=hv (oneAmbientCoordinates N w)
    simpa only [oneAmbientPolar,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply] using h

theorem one_polar_matrix_inj (N : ℕ) : Function.Injective (onePolarMatrix N).mulVec := by
  have h:=LinearMap.Nondegenerate.toMatrix₂' (one_ambient_polar_nondegenerate N)
  intro v w he
  apply sub_eq_zero.mp
  apply h.separatingRight.eq_zero_of_mulVec_eq_zero
  exact (Matrix.mulVec_sub _ v w).trans (sub_eq_zero.mpr he)

variable {p : Shape} {n N : ℕ}
abbrev OneCross (p : Shape) (n : ℕ) := ImageCross (Comp p.g) (OneColumn p n)

def oneCrossMatrix (x y : OneUnit p n N) : OneCross p n:=fun e=>
  LinearMap.toMatrix₂' F ((oneUnitActual x y e).compl₁₂
    (oneNominalCoordinates p n).toLinearMap (oneNominalCoordinates p n).toLinearMap)

def oneTableOfCross (Q : OneCross p n) (e : Comp p.g) :
    LinearMap.BilinForm F (OneUnitFull p n):=
  (Q e).toBilin'.compl₁₂ (oneNominalCoordinates p n).symm.toLinearMap
    (oneNominalCoordinates p n).symm.toLinearMap

theorem one_actual_table (x y : OneUnit p n N) (e : Comp p.g) :
    oneTableOfCross (oneCrossMatrix x y) e=oneUnitActual x y e := by
  have he : (oneCrossMatrix x y e).toBilin'=(oneUnitActual x y e).compl₁₂
      (oneNominalCoordinates p n).toLinearMap (oneNominalCoordinates p n).toLinearMap:=
    Matrix.toBilin'_toMatrix' _
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  simp only [oneTableOfCross,he,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem one_cross_matrix_images (x y : OneUnit p n N) :
    oneCrossMatrix x y=imageActual oneCoordinateImages
      (fun y e=>onePolarMatrix N*oneCoordinateImages y e) x y := by
  funext e
  let P:=(oneAmbientCoordinates N).toLinearMap.comp
    ((oneUnitMap x e).comp (oneNominalCoordinates p n).toLinearMap)
  let Q:=(oneAmbientCoordinates N).toLinearMap.comp
    ((oneUnitMap y e).comp (oneNominalCoordinates p n).toLinearMap)
  have he : (oneUnitActual x y e).compl₁₂
      (oneNominalCoordinates p n).toLinearMap (oneNominalCoordinates p n).toLinearMap=
      (oneAmbientPolar N).compl₁₂ P Q := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    simp only [P,Q,oneAmbientPolar,oneUnitActual,LinearMap.compl₁₂_apply,
      LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  unfold oneCrossMatrix
  rw [he,LinearMap.toMatrix₂'_compl₁₂]
  exact Matrix.mul_assoc _ _ _

variable {V : Type} [AddCommGroup V] [Module F V] [Fintype V]

/-- The concrete one-frame cross-Gram test has the same quantitative
hit guarantee on independently sampled spreading leaves. -/
theorem one_gram_hit (Q : OneCross p n) (T : OneCross p n→ₗ[F]V)
    {u w : Wgt (OneUnit p n N)} (hu : IsLaw u) (hw : IsLaw w)
    {a b : ImagePin (Comp p.g) (OneColumn p n) (2*N)}
    (hc : imagePinClear oneCoordinateImages a 0.05 u)
    (hd : imagePinClear oneCoordinateImages b 0.05 w)
    (h : ∀ x,u x≠0→∀ y,w y≠0→imageRowAgree a.sp (oneCrossMatrix x y) Q ∧
      imageRowAgree b.sp (fun e=>(oneCrossMatrix x y e)ᵀ) (fun e=>(Q e)ᵀ))
    (hN : 100≤2*N) (hT : (dim V:ℝ)≤0.01*(2*N)) :
    hit (2*N)≤pr (pairW u w) (fun x=>T (oneCrossMatrix x.1 x.2)=T Q) := by
  simp_rw [one_cross_matrix_images] at h ⊢
  exact image_polar_gram_hit oneCoordinateImages oneCoordinateImages
    (fun _=>onePolarMatrix N) (fun _=>one_polar_matrix_inj N) Q T hu hw hc hd h hN
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hT)

end
end Lax793645Proofs.Simplifications
