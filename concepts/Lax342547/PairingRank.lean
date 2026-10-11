import Lax342547.CoverSpace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
---
title: Tiny-cover pairing matrix rank
type: definition and theorem
---
The actual pairing matrix factors through the covered tensor space; its rank is bounded by the two mode dimensions times their ambient dimensions.
-/

namespace Lax342547.PairingRank

open Lax342547.CoverProjection
open scoped BigOperators

axiom pairing_matrix_rank_le {K V Ω : Type} [Field K] [Fintype Ω]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Submodule K V) (v : Ω → V) (hv : ∀ a, v a ∈ S) (φ : Ω → Module.Dual K V) :
    (Matrix.of (fun a b => φ b (v a))).rank ≤ Module.finrank K S

axiom covered_pairing_rank {K V W Ω : Type} [Field K] [Fintype Ω]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (Δ : Ω → V →ₗ[K] W) (φ : Ω → Module.Dual K (V →ₗ[K] W))
    (hΔ : ∀ a, projection (Δ a) S T = 0) :
    (Matrix.of (fun a b => φ b (Δ a))).rank ≤
      Module.finrank K V*Module.finrank K S+Module.finrank K T*Module.finrank K W

end Lax342547.PairingRank
