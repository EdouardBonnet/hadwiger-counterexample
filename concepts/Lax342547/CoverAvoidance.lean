import Lax342547.CoverProjection

/-!
---
title: Rank preservation under mode-cover avoidance
type: lemma
---
Actual quotient and annihilator restriction preserve rank when the original column and row spaces avoid the cover.
-/

namespace Lax342547.CoverAvoidance

open Lax342547.CoverProjection

axiom finrank_map_of_disjoint_kernel {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (S : Submodule K V) (h : Disjoint S (LinearMap.ker f)) :
    Module.finrank K (S.map f) = Module.finrank K S

axiom quotient_rank_of_avoidance {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : V →ₗ[K] W) (S : Submodule K W) (h : Disjoint (LinearMap.range M) S) :
    Module.finrank K (LinearMap.range (S.mkQ.comp M)) = Module.finrank K (LinearMap.range M)

axiom restriction_rank_of_avoidance {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : V →ₗ[K] W) (T : Submodule K (Module.Dual K V))
    (h : Disjoint (LinearMap.range M.dualMap) T) :
    Module.finrank K (LinearMap.range (M.comp T.dualCoannihilator.subtype)) =
      Module.finrank K (LinearMap.range M)

axiom projection_rank_of_avoidance {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : V →ₗ[K] W) (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (hS : Disjoint (LinearMap.range M) S) (hT : Disjoint (LinearMap.range M.dualMap) T) :
    Module.finrank K (LinearMap.range (projection M S T)) = Module.finrank K (LinearMap.range M)

end Lax342547.CoverAvoidance
