import Lax342547.Counterexample
import Lax342547Proofs.HadwigerMatching.MinorBound
import Lax342547Proofs.HadwigerMatching.ChromaticBound
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.Counterexample

open Lax342547.ConnectedMatching Lax342547.CliqueMinor

/-- The final finite counting implication, with no graph-existence assumption. -/
theorem hadwiger_lt_chromatic_of_small_connected_matching
    {V : Type} [Fintype V] (G : SimpleGraph V)
    (hα : G.indepNum ≤ 2) (hc : 100 * connectedMatchingNumber G < Fintype.card V)
    (hm : 5 ≤ Fintype.card V) :
    hadwigerNumber G < G.chromaticNumber.toNat := by
  have hminor := HadwigerMatching.hadwiger_matching_bound G
  have hchrom := HadwigerMatching.card_le_twice_chromaticNumber_of_indepNum G hα
  omega

/--
---
conclusion: Lax342547.Counterexample.arbitrarily_large_hadwiger_counterexample
assumptions:
  - Lax342547.Counterexample.arbitrarily_large_small_connected_matching
---
Theorem 1.1 supplies the graph. The proved matching-minor bound and
chromatic lower bound then contradict Hadwiger's inequality.
-/
theorem arbitrarily_large_hadwiger_counterexample (lowerBound : ℕ) :
    ∃ m : ℕ, lowerBound ≤ m ∧ 5 ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ hadwigerNumber G < G.chromaticNumber.toNat := by
  obtain ⟨m, hm, G, hα, hc⟩ :=
    Lax342547.Counterexample.arbitrarily_large_small_connected_matching (max lowerBound 5)
  refine ⟨m, (le_max_left _ _).trans hm, (le_max_right _ _).trans hm, G, hα, ?_⟩
  apply hadwiger_lt_chromatic_of_small_connected_matching G hα
  · simpa using hc
  · simpa using (le_max_right lowerBound 5).trans hm

end Lax342547Proofs.Counterexample
