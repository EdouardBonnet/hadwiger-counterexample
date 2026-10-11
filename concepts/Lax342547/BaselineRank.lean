import Lax342547.PrimalRetractions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-!
---
title: Rank control for the frozen baseline on primal inputs
type: lemma
---
Retract the primal inputs before constructing the baseline. Its channel
evaluation factors through the bounded primal retraction and the dual of
the opposite pin space. This separates the two costs and avoids paying
for arbitrary channel-channel entries of the table.
-/

namespace Lax342547.BaselineRank

open Lax342547.MomentSpace Lax342547.FrozenBaselines

variable {V W C : Type} [AddCommGroup V] [Module Binary V]
  [AddCommGroup W] [Module Binary W] [AddCommGroup C] [Module Binary C]

def retracted {J D Keys : Submodule Binary V} (S : Splitting J D Keys)
    (hD : D ≤ J) (p : V →ₗ[Binary] V) (hfix : ∀ v ∈ J ⊔ Keys, p v = v) :
    Splitting J D Keys where
  frozen := S.frozen.comp p
  table := S.table.comp p
  frozen_fixed v hv := by
    rw [LinearMap.comp_apply, hfix v ((sup_le_sup hD le_rfl) hv)]
    exact S.frozen_fixed v hv
  table_zero v hv := by
    rw [LinearMap.comp_apply, hfix v ((sup_le_sup hD le_rfl) hv)]
    exact S.table_zero v hv
  frozen_table v := by
    rw [LinearMap.comp_apply, hfix v.val ((show J ≤ J ⊔ Keys from le_sup_left) v.property)]
    exact S.frozen_table v
  table_sum v := by
    simp only [LinearMap.comp_apply, hfix v.val ((show J ≤ J ⊔ Keys from le_sup_left) v.property)]
    exact S.table_sum v

axiom channel_rank [FiniteDimensional Binary V] [FiniteDimensional Binary W]
    (J D Keys U : Submodule Binary V) (J' D' Keys' : Submodule Binary W)
    (hD : D ≤ J) (S : Splitting J D Keys) (S' : Splitting J' D' Keys')
    (p : V →ₗ[Binary] V) (hfix : ∀ v ∈ J ⊔ Keys, p v = v)
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary)
    (q : C →ₗ[Binary] J') :
    Module.finrank Binary (LinearMap.range
      ((baseline (retracted S hD p hfix) S' A T).compl₁₂ U.subtype (J'.subtype.comp q))) ≤
      Module.finrank Binary (LinearMap.range (p.comp U.subtype)) + Module.finrank Binary D'

axiom bounded_baseline [FiniteDimensional Binary V] [FiniteDimensional Binary W]
    (J D Keys U : Submodule Binary V) (J' D' Keys' U' : Submodule Binary W)
    (hD : D ≤ J) (hD' : D' ≤ J') (hKeys : Disjoint J Keys) (hKeys' : Disjoint J' Keys')
    (hspan : J ⊔ U = ⊤) (hKeyPrimal : Keys ≤ U)
    (hspan' : J' ⊔ U' = ⊤) (hKeyPrimal' : Keys' ≤ U')
    (A : V →ₗ[Binary] W →ₗ[Binary] Binary) (T : J →ₗ[Binary] J' →ₗ[Binary] Binary)
    (h : Compatible J D J' D' A T) :
    ∃ B : V →ₗ[Binary] W →ₗ[Binary] Binary,
      ExtendsFrozen D Keys D' Keys' A B ∧ (∀ v : J, ∀ w : J', B v.val w.val = T v w) ∧
      (∀ q : C →ₗ[Binary] J',
        Module.finrank Binary (LinearMap.range (B.compl₁₂ U.subtype (J'.subtype.comp q))) ≤
          Module.finrank Binary ↥(J ⊓ U) + Module.finrank Binary Keys + Module.finrank Binary D') ∧
      ∀ q : C →ₗ[Binary] J,
        Module.finrank Binary (LinearMap.range (B.flip.compl₁₂ U'.subtype (J.subtype.comp q))) ≤
          Module.finrank Binary ↥(J' ⊓ U') + Module.finrank Binary Keys' + Module.finrank Binary D

end Lax342547.BaselineRank
