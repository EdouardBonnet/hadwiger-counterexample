import Lax342547.FrozenBaselines
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
---
title: Retractions with bounded rank on the primal inputs
type: theorem
---
When the table together with the primal space spans the nominal space,
one can retract onto table plus keys while preserving the primal space.
The rank on primal inputs costs only table-primal directions and keys,
and does not count the channel dimension.
-/

namespace Lax342547.PrimalRetractions

open Lax342547.MomentSpace

axiom bounded_retraction {V : Type} [AddCommGroup V] [Module Binary V]
    [FiniteDimensional Binary V] (J Keys U : Submodule Binary V)
    (hspan : J ⊔ U = ⊤) (hKeys : Keys ≤ U) :
    ∃ p : V →ₗ[Binary] V,
      (∀ v, p v ∈ J ⊔ Keys) ∧ (∀ v ∈ J ⊔ Keys, p v = v) ∧
      (∀ v ∈ U, p v ∈ U) ∧
      Module.finrank Binary (LinearMap.range (p.comp U.subtype)) ≤
        Module.finrank Binary ↥(J ⊓ U) + Module.finrank Binary Keys

end Lax342547.PrimalRetractions
