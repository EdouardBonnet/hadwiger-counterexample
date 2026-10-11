import Lax342547.CoverAvoidance
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
---
title: Actual factor lifts and covered offsets
type: lemma
---
Common minimal quotient factors lift to actual endpoint factors, with covered differences, independent companion spaces, and the precise offset dimension budget.
-/

namespace Lax342547.QuotientFactorLifts



axiom lift_common_factor {K D U V W X : Type} [Field K]
    [AddCommGroup D] [Module K D] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X]
    (π : W →ₗ[K] X) (C : U →ₗ[K] X) (M : V →ₗ[K] W)
    (B : D →ₗ[K] V) (R : D →ₗ[K] U)
    (hC : Function.Injective C) (hR : Function.Surjective R)
    (hπ : Disjoint (LinearMap.range M) (LinearMap.ker π))
    (hrange : LinearMap.range (M.comp B) = LinearMap.range M)
    (hcommon : π.comp (M.comp B) = C.comp R) :
    ∃ P : U →ₗ[K] W, ∃ Q : V →ₗ[K] U,
      P.comp Q = M ∧ π.comp P = C ∧ Q.comp B = R

axiom restriction_range_of_avoidance {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : V →ₗ[K] W) (T : Submodule K (Module.Dual K V))
    (hT : Disjoint (LinearMap.range M.dualMap) T) :
    LinearMap.range (M.comp T.dualCoannihilator.subtype) = LinearMap.range M

axiom lift_quotient_factor {K U V W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (C : U →ₗ[K] (W ⧸ S)) (M : V →ₗ[K] W) (R : T.dualCoannihilator →ₗ[K] U)
    (hC : Function.Injective C) (hR : Function.Surjective R)
    (hS : Disjoint (LinearMap.range M) S) (hT : Disjoint (LinearMap.range M.dualMap) T)
    (hfactor : Lax342547.CoverProjection.projection M S T = C.comp R) :
    ∃ P : U →ₗ[K] W, ∃ Q : V →ₗ[K] U,
      P.comp Q = M ∧ S.mkQ.comp P = C ∧ Q.comp T.dualCoannihilator.subtype = R

axiom column_difference_in_cover {K U W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (C : U →ₗ[K] (W ⧸ S)) (P₁ P₂ : U →ₗ[K] W)
    (h₁ : S.mkQ.comp P₁ = C) (h₂ : S.mkQ.comp P₂ = C) :
    LinearMap.range (P₁-P₂) ≤ S

axiom row_difference_in_cover {K U V : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (T : Submodule K (Module.Dual K V)) (R : T.dualCoannihilator →ₗ[K] U)
    (Q₁ Q₂ : V →ₗ[K] U)
    (h₁ : Q₁.comp T.dualCoannihilator.subtype = R)
    (h₂ : Q₂.comp T.dualCoannihilator.subtype = R) :
    LinearMap.range (Q₁-Q₂).dualMap ≤ T

axiom factor_difference_identity {K U V W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (P₁ P₂ : U →ₗ[K] W) (Q₁ Q₂ : V →ₗ[K] U) :
    P₁.comp Q₁-P₂.comp Q₂ = (P₁-P₂).comp Q₂+P₁.comp (Q₁-Q₂)

axiom lifted_column_avoids_cover {K U W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (C : U →ₗ[K] (W ⧸ S)) (P : U →ₗ[K] W)
    (hC : Function.Injective C) (hP : S.mkQ.comp P = C) :
    Disjoint (LinearMap.range P) S

axiom offset_dimension_budget {K U V W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K U]
    (P : U →ₗ[K] W) (Q : V →ₗ[K] U) :
    Module.finrank K (LinearMap.range P)+Module.finrank K (LinearMap.range Q.dualMap) ≤
      2*Module.finrank K U

axiom lifted_row_avoids_cover {K U V : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (T : Submodule K (Module.Dual K V)) (R : T.dualCoannihilator →ₗ[K] U)
    (Q : V →ₗ[K] U) (hR : Function.Surjective R)
    (hQ : Q.comp T.dualCoannihilator.subtype = R) :
    Disjoint (LinearMap.range Q.dualMap) T

axiom common_quotient_offsets {K U V W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K U]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (C : U →ₗ[K] (W ⧸ S)) (R : T.dualCoannihilator →ₗ[K] U)
    (M₁ M₂ : V →ₗ[K] W) (hC : Function.Injective C) (hR : Function.Surjective R)
    (hS₁ : Disjoint (LinearMap.range M₁) S) (hT₁ : Disjoint (LinearMap.range M₁.dualMap) T)
    (hS₂ : Disjoint (LinearMap.range M₂) S) (hT₂ : Disjoint (LinearMap.range M₂.dualMap) T)
    (h₁ : Lax342547.CoverProjection.projection M₁ S T = C.comp R)
    (h₂ : Lax342547.CoverProjection.projection M₂ S T = C.comp R) :
    ∃ P₁ P₂ : U →ₗ[K] W, ∃ Q₁ Q₂ : V →ₗ[K] U,
      P₁.comp Q₁ = M₁ ∧ P₂.comp Q₂ = M₂ ∧
      LinearMap.range (P₁-P₂) ≤ S ∧ LinearMap.range (Q₁-Q₂).dualMap ≤ T ∧
      Disjoint (LinearMap.range P₁) S ∧ Disjoint (LinearMap.range Q₂.dualMap) T ∧
      M₁-M₂ = (P₁-P₂).comp Q₂+P₁.comp (Q₁-Q₂) ∧
      Module.finrank K (LinearMap.range (P₁-P₂))+
        Module.finrank K (LinearMap.range (Q₁-Q₂).dualMap) ≤ 2*Module.finrank K U

end Lax342547.QuotientFactorLifts
