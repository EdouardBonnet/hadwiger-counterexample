import Lax342547.DirectRanks
import Lax342547Proofs.RestrictionRank
import Mathlib.LinearAlgebra.Pi

namespace Lax342547Proofs.DirectRanks
open Lax342547.DirectRanks

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/--
---
conclusion: Lax342547.DirectRanks.diagonal_rank_sum
---
-/
theorem diagonal_rank_sum {K ι : Type} [Field K] [Fintype ι]
    {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (W i)] (M : ∀ i, V i →ₗ[K] W i) :
    Module.finrank K (LinearMap.range (LinearMap.piMap M)) =
      ∑ i, Module.finrank K (LinearMap.range (M i)) := by
  rw [(rangeProductEquiv M).finrank_eq]
  exact Module.finrank_pi_fintype K

end Lax342547Proofs.DirectRanks
