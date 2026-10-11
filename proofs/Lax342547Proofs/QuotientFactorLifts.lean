import Lax342547.QuotientFactorLifts
import Lax342547Proofs.CoverAvoidance
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Lax342547Proofs.QuotientFactorLifts
open Lax342547.QuotientFactorLifts

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.QuotientFactorLifts.lift_common_factor
---
-/
theorem lift_common_factor {K D U V W X : Type} [Field K]
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
      P.comp Q = M ∧ π.comp P = C ∧ Q.comp B = R := by
  obtain ⟨L,hL⟩ := C.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hC)
  let Q := L.comp (π.comp M)
  have hQ : Q.comp B = R := by
    dsimp [Q]
    simp only [LinearMap.comp_assoc]
    rw [hcommon,← LinearMap.comp_assoc,hL,LinearMap.id_comp]
  have hQs : Function.Surjective Q := by
    intro u
    obtain ⟨v,hv⟩ := hR u
    refine ⟨B v,?_⟩
    have he := congrArg (fun f : D →ₗ[K] U => f v) hQ
    exact he.trans hv
  have hcol : LinearMap.range (π.comp M) ≤ LinearMap.range C := by
    have he : LinearMap.range (π.comp (M.comp B)) = LinearMap.range (π.comp M) := by
      rw [LinearMap.range_comp,hrange,LinearMap.range_comp]
    rw [← he,hcommon,LinearMap.range_comp]
    exact LinearMap.map_le_range
  have hCQ : C.comp Q = π.comp M := by
    apply LinearMap.ext
    intro v
    obtain ⟨u,hu⟩ := hcol (LinearMap.mem_range_self (π.comp M) v)
    change C (L (π (M v))) = π (M v)
    change C u = π (M v) at hu
    rw [← hu]
    have he := congrArg (fun f : U →ₗ[K] U => f u) hL
    change L (C u) = u at he
    rw [he]
  have hker (v : V) (hv : Q v = 0) : M v = 0 := by
    have he := congrArg (fun f : V →ₗ[K] X => f v) hCQ
    change C (Q v) = π (M v) at he
    rw [hv,map_zero] at he
    have hm : M v ∈ LinearMap.range M ⊓ LinearMap.ker π :=
      ⟨LinearMap.mem_range_self M v,LinearMap.mem_ker.mpr he.symm⟩
    rw [hπ.eq_bot] at hm
    exact hm
  obtain ⟨I,hI⟩ := Q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hQs)
  let P := M.comp I
  refine ⟨P,Q,?_,?_,hQ⟩
  · apply LinearMap.ext
    intro v
    have hi := congrArg (fun f : U →ₗ[K] U => f (Q v)) hI
    change Q (I (Q v)) = Q v at hi
    have hk := hker (I (Q v)-v) (by rw [map_sub,hi,sub_self])
    rw [map_sub] at hk
    exact sub_eq_zero.mp hk
  · dsimp [P]
    rw [← LinearMap.comp_assoc,← hCQ,LinearMap.comp_assoc,hI,LinearMap.comp_id]

/--
---
conclusion: Lax342547.QuotientFactorLifts.restriction_range_of_avoidance
---
-/
theorem restriction_range_of_avoidance {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : V →ₗ[K] W) (T : Submodule K (Module.Dual K V))
    (hT : Disjoint (LinearMap.range M.dualMap) T) :
    LinearMap.range (M.comp T.dualCoannihilator.subtype) = LinearMap.range M := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [LinearMap.range_comp]
    exact LinearMap.map_le_range
  · exact Lax342547Proofs.CoverAvoidance.restriction_rank_of_avoidance M T hT

/--
---
conclusion: Lax342547.QuotientFactorLifts.lift_quotient_factor
---
-/
theorem lift_quotient_factor {K U V W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (C : U →ₗ[K] (W ⧸ S)) (M : V →ₗ[K] W) (R : T.dualCoannihilator →ₗ[K] U)
    (hC : Function.Injective C) (hR : Function.Surjective R)
    (hS : Disjoint (LinearMap.range M) S) (hT : Disjoint (LinearMap.range M.dualMap) T)
    (hfactor : Lax342547.CoverProjection.projection M S T = C.comp R) :
    ∃ P : U →ₗ[K] W, ∃ Q : V →ₗ[K] U,
      P.comp Q = M ∧ S.mkQ.comp P = C ∧ Q.comp T.dualCoannihilator.subtype = R := by
  exact lift_common_factor S.mkQ C M T.dualCoannihilator.subtype R hC hR
    (by simpa only [Submodule.ker_mkQ] using hS)
    (restriction_range_of_avoidance M T hT) hfactor

/--
---
conclusion: Lax342547.QuotientFactorLifts.column_difference_in_cover
---
-/
theorem column_difference_in_cover {K U W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (C : U →ₗ[K] (W ⧸ S)) (P₁ P₂ : U →ₗ[K] W)
    (h₁ : S.mkQ.comp P₁ = C) (h₂ : S.mkQ.comp P₂ = C) :
    LinearMap.range (P₁-P₂) ≤ S := by
  rintro _ ⟨u,rfl⟩
  rw [← Submodule.ker_mkQ S]
  apply LinearMap.mem_ker.mpr
  have h₁u := congrArg (fun f : U →ₗ[K] (W ⧸ S) => f u) h₁
  have h₂u := congrArg (fun f : U →ₗ[K] (W ⧸ S) => f u) h₂
  simp only [LinearMap.comp_apply] at h₁u h₂u
  simp only [LinearMap.sub_apply,map_sub,h₁u,h₂u,sub_self]

/--
---
conclusion: Lax342547.QuotientFactorLifts.row_difference_in_cover
---
-/
theorem row_difference_in_cover {K U V : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (T : Submodule K (Module.Dual K V)) (R : T.dualCoannihilator →ₗ[K] U)
    (Q₁ Q₂ : V →ₗ[K] U)
    (h₁ : Q₁.comp T.dualCoannihilator.subtype = R)
    (h₂ : Q₂.comp T.dualCoannihilator.subtype = R) :
    LinearMap.range (Q₁-Q₂).dualMap ≤ T := by
  have hk : T.dualCoannihilator ≤ LinearMap.ker (Q₁-Q₂) := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    have h₁v := congrArg (fun f : T.dualCoannihilator →ₗ[K] U => f ⟨v,hv⟩) h₁
    have h₂v := congrArg (fun f : T.dualCoannihilator →ₗ[K] U => f ⟨v,hv⟩) h₂
    change Q₁ v = R ⟨v,hv⟩ at h₁v
    change Q₂ v = R ⟨v,hv⟩ at h₂v
    simp only [LinearMap.sub_apply,h₁v,h₂v,sub_self]
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  simpa only [Subspace.dualCoannihilator_dualAnnihilator_eq] using Submodule.dualAnnihilator_anti hk

/--
---
conclusion: Lax342547.QuotientFactorLifts.factor_difference_identity
---
-/
theorem factor_difference_identity {K U V W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (P₁ P₂ : U →ₗ[K] W) (Q₁ Q₂ : V →ₗ[K] U) :
    P₁.comp Q₁-P₂.comp Q₂ = (P₁-P₂).comp Q₂+P₁.comp (Q₁-Q₂) := by
  rw [LinearMap.sub_comp,LinearMap.comp_sub]
  abel

/--
---
conclusion: Lax342547.QuotientFactorLifts.lifted_column_avoids_cover
---
-/
theorem lifted_column_avoids_cover {K U W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (C : U →ₗ[K] (W ⧸ S)) (P : U →ₗ[K] W)
    (hC : Function.Injective C) (hP : S.mkQ.comp P = C) :
    Disjoint (LinearMap.range P) S := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨u,hu⟩ := hx.1
  have hz : C u = 0 := by
    have he := congrArg (fun f : U →ₗ[K] (W ⧸ S) => f u) hP
    change S.mkQ (P u) = C u at he
    have hx0 : S.mkQ x = 0 := by
      apply LinearMap.mem_ker.mp
      rw [Submodule.ker_mkQ]
      exact hx.2
    rw [hu,hx0] at he
    exact he.symm
  have hu0 : u = 0 := hC (hz.trans (map_zero C).symm)
  have he : x = 0 := by simpa only [hu0,map_zero] using hu.symm
  simpa only [he] using (show (0 : W) ∈ (⊥ : Submodule K W) from Submodule.zero_mem _)

/--
---
conclusion: Lax342547.QuotientFactorLifts.offset_dimension_budget
---
-/
theorem offset_dimension_budget {K U V W : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K U]
    (P : U →ₗ[K] W) (Q : V →ₗ[K] U) :
    Module.finrank K (LinearMap.range P)+Module.finrank K (LinearMap.range Q.dualMap) ≤
      2*Module.finrank K U := by
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range]
  have hP := LinearMap.finrank_range_le P
  have hQ := Submodule.finrank_le (LinearMap.range Q)
  omega

/--
---
conclusion: Lax342547.QuotientFactorLifts.lifted_row_avoids_cover
---
-/
theorem lifted_row_avoids_cover {K U V : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    (T : Submodule K (Module.Dual K V)) (R : T.dualCoannihilator →ₗ[K] U)
    (Q : V →ₗ[K] U) (hR : Function.Surjective R)
    (hQ : Q.comp T.dualCoannihilator.subtype = R) :
    Disjoint (LinearMap.range Q.dualMap) T := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  intro φ hφ
  obtain ⟨f,hf⟩ := hφ.1
  have hzero : f = 0 := by
    apply LinearMap.ext
    intro u
    obtain ⟨v,hv⟩ := hR u
    have he := congrArg (fun F : T.dualCoannihilator →ₗ[K] U => F v) hQ
    change Q v.val = R v at he
    have hφv : φ v.val = 0 := ((Submodule.mem_dualCoannihilator v.val).mp v.property) φ hφ.2
    have hf' := congrArg (fun F : Module.Dual K V => F v.val) hf
    change f (Q v.val) = φ v.val at hf'
    rw [he,hv] at hf'
    simpa only [LinearMap.zero_apply] using hf'.trans hφv
  have he : φ = 0 := by simpa only [hzero,map_zero] using hf.symm
  simpa only [he] using (show (0 : Module.Dual K V) ∈ (⊥ : Submodule K (Module.Dual K V)) from Submodule.zero_mem _)

/--
---
conclusion: Lax342547.QuotientFactorLifts.common_quotient_offsets
---
-/
theorem common_quotient_offsets {K U V W : Type} [Field K]
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
        Module.finrank K (LinearMap.range (Q₁-Q₂).dualMap) ≤ 2*Module.finrank K U := by
  obtain ⟨P₁,Q₁,hPQ₁,hP₁,hQ₁⟩ := lift_quotient_factor S T C M₁ R hC hR hS₁ hT₁ h₁
  obtain ⟨P₂,Q₂,hPQ₂,hP₂,hQ₂⟩ := lift_quotient_factor S T C M₂ R hC hR hS₂ hT₂ h₂
  refine ⟨P₁,P₂,Q₁,Q₂,hPQ₁,hPQ₂,column_difference_in_cover S C P₁ P₂ hP₁ hP₂,
    row_difference_in_cover T R Q₁ Q₂ hQ₁ hQ₂,lifted_column_avoids_cover S C P₁ hC hP₁,
    lifted_row_avoids_cover T R Q₂ hR hQ₂,?_,offset_dimension_budget (P₁-P₂) (Q₁-Q₂)⟩
  rw [← hPQ₁,← hPQ₂]
  exact factor_difference_identity P₁ P₂ Q₁ Q₂

end Lax342547Proofs.QuotientFactorLifts
