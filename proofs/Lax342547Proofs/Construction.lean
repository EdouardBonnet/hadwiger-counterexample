import Lax342547.Counterexample
import Lax342547Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.Main

/-!
The complete binary-frame construction, adapted from the pinned upstream
development, proves the local Theorem 1.1 statement. The two touching-matching
definitions are definitionally equal; only the arithmetic form of the bound
changes. No graph-existence or supersaturation hypothesis is assumed here.
-/

namespace Lax342547Proofs.Construction

open Lax342547.ConnectedMatching

/-- The upstream and archive matching numbers use exactly the same definition. -/
theorem connectedMatchingNumber_eq {V : Type} (G : SimpleGraph V) :
    connectedMatchingNumber G =
      Upstream.OAI.HadwigerMatching.connectedMatchingNumber G := rfl

/--
---
conclusion: Lax342547.Counterexample.arbitrarily_large_small_connected_matching
---
The complete binary-frame construction produces graphs of arbitrarily large
order. Its touching-matching number is the archive's matching number by
definitional equality, and the strict rational bound gives the integral bound.
-/
theorem arbitrarily_large_small_connected_matching (lowerBound : ℕ) :
    ∃ m : ℕ, lowerBound ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ 100 * connectedMatchingNumber G < m := by
  obtain ⟨m, hm, G, hα, hc⟩ :=
    Upstream.OAI.HadwigerCounterexample.exists_graphs lowerBound
  refine ⟨m, (le_max_left _ _).trans hm, G, hα, ?_⟩
  rw [← connectedMatchingNumber_eq G] at hc
  have h100 : (100 : ℚ) * (connectedMatchingNumber G : ℚ) < (m : ℚ) := by
    linarith
  exact_mod_cast h100

end Lax342547Proofs.Construction
