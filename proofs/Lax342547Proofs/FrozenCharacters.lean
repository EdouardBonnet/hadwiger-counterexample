import Lax342547.FrozenCharacters
import Lax342547Proofs.TensorAnnihilators
import Lax342547Proofs.ResidualRealization
import Mathlib.LinearAlgebra.Quotient.Defs

namespace Lax342547Proofs.FrozenCharacters
open Lax342547.FrozenCharacters

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TensorAnnihilators

/--
---
conclusion: Lax342547.FrozenCharacters.quotient_bilinear
---
-/
theorem quotient_bilinear {V W : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W]
    (D : Submodule Binary V) (E : Submodule Binary W)
    (F : V →ₗ[Binary] W →ₗ[Binary] Binary)
    (hD : ∀ v ∈ D, ∀ w, F v w = 0) (hE : ∀ v w, w ∈ E → F v w = 0) :
    ∃ Q : (V ⧸ D) →ₗ[Binary] (W ⧸ E) →ₗ[Binary] Binary,
      Q.compl₁₂ D.mkQ E.mkQ = F := by
  let inner : V →ₗ[Binary] (W ⧸ E) →ₗ[Binary] Binary :=
    { toFun := fun v => E.liftQ (F v) (by intro w hw; exact hE v w hw)
      map_add' := by
        intro v v'
        apply LinearMap.ext
        intro w
        induction w using Submodule.Quotient.induction_on with
        | H w => simp
      map_smul' := by
        intro c v
        apply LinearMap.ext
        intro w
        induction w using Submodule.Quotient.induction_on with
        | H w => simp }
  refine ⟨D.liftQ inner ?_, ?_⟩
  · intro v hv
    apply LinearMap.ext
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H w => exact hD v hv w
  · apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    rfl

/--
---
conclusion: Lax342547.FrozenCharacters.zero_quotient_frozen_agreement
---
-/
theorem zero_quotient_frozen_agreement {I : Type} [Fintype I]
    (C : Matrix I I Binary) (D E : Submodule Binary (I → Binary))
    (F G : (I → Binary) →ₗ[Binary] (I → Binary) →ₗ[Binary] Binary)
    (hC : PureAnnihilates C D E)
    (hD : ∀ v ∈ D, ∀ w, F v w = G v w)
    (hE : ∀ v w, w ∈ E → F v w = G v w) :
    by
      classical
      exact matrixPair (LinearMap.BilinForm.toMatrix' F) C =
        matrixPair (LinearMap.BilinForm.toMatrix' G) C := by
  classical
  obtain ⟨Q, hQ⟩ := quotient_bilinear D E (F - G)
    (fun v hv w => by simp only [LinearMap.sub_apply, sub_eq_zero]; exact hD v hv w)
    (fun v w hw => by simp only [LinearMap.sub_apply, sub_eq_zero]; exact hE v w hw)
  have h := hC Q
  unfold pureContraction at h
  rw [hQ] at h
  have hm : LinearMap.BilinForm.toMatrix' (F - G) =
      LinearMap.BilinForm.toMatrix' F - LinearMap.BilinForm.toMatrix' G := by
    ext i j
    rfl
  rw [hm] at h
  rw [Lax342547Proofs.ResidualRealization.matrixPair_sub, LinearMap.sub_apply] at h
  exact sub_eq_zero.mp h

end Lax342547Proofs.FrozenCharacters
