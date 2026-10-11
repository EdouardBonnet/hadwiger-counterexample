import Lax342547.ProjectedOffsets
import Lax342547Proofs.QuotientFactorLifts

namespace Lax342547Proofs.ProjectedOffsets
open Lax342547.ProjectedOffsets

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.ProjectedOffsets.actual_common_projection_offsets
---
-/
theorem actual_common_projection_offsets {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) (M₁ M₂ : V →ₗ[K] W)
    (hS₁ : Disjoint (LinearMap.range M₁) S) (hT₁ : Disjoint (LinearMap.range M₁.dualMap) T)
    (hS₂ : Disjoint (LinearMap.range M₂) S) (hT₂ : Disjoint (LinearMap.range M₂.dualMap) T)
    (hcommon : Lax342547.CoverProjection.projection M₁ S T = Lax342547.CoverProjection.projection M₂ S T) :
    ∃ P₁ P₂ : LinearMap.range (Lax342547.CoverProjection.projection M₁ S T) →ₗ[K] W,
    ∃ Q₁ Q₂ : V →ₗ[K] LinearMap.range (Lax342547.CoverProjection.projection M₁ S T),
      P₁.comp Q₁ = M₁ ∧ P₂.comp Q₂ = M₂ ∧
      LinearMap.range (P₁-P₂) ≤ S ∧ LinearMap.range (Q₁-Q₂).dualMap ≤ T ∧
      Disjoint (LinearMap.range P₁) S ∧ Disjoint (LinearMap.range Q₂.dualMap) T ∧
      M₁-M₂ = (P₁-P₂).comp Q₂+P₁.comp (Q₁-Q₂) ∧
      Module.finrank K (LinearMap.range (P₁-P₂))+
        Module.finrank K (LinearMap.range (Q₁-Q₂).dualMap) ≤
        2*Module.finrank K (LinearMap.range (Lax342547.CoverProjection.projection M₁ S T)) := by
  let F := Lax342547.CoverProjection.projection M₁ S T
  apply Lax342547Proofs.QuotientFactorLifts.common_quotient_offsets S T
    (LinearMap.range F).subtype F.rangeRestrict M₁ M₂
    (LinearMap.range F).injective_subtype (by rintro ⟨z,hz⟩; obtain ⟨v,rfl⟩ := hz; exact ⟨v,rfl⟩) hS₁ hT₁ hS₂ hT₂
  · exact rfl
  · rw [← hcommon]
    exact rfl

/--
---
conclusion: Lax342547.ProjectedOffsets.nonzero_difference_has_offset
---
-/
theorem nonzero_difference_has_offset {K U V W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (P₁ P₂ : U →ₗ[K] W) (Q₁ Q₂ : V →ₗ[K] U)
    (hne : P₁.comp Q₁ ≠ P₂.comp Q₂) : P₁-P₂ ≠ 0 ∨ Q₁-Q₂ ≠ 0 := by
  by_contra hn
  push Not at hn
  have hP := sub_eq_zero.mp hn.1
  have hQ := sub_eq_zero.mp hn.2
  exact hne (by rw [hP,hQ])

end Lax342547Proofs.ProjectedOffsets
