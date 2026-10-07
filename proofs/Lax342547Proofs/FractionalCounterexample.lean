import Lax342547.Counterexample
import Lax342547.FractionalCounterexample
import Lax342547Proofs.HadwigerMatching.MinorBound
import Lax342547Proofs.FractionalColoring
import Mathlib.Tactic.NormNum

namespace Lax342547Proofs.FractionalCounterexample

open Lax342547.ConnectedMatching Lax342547.CliqueMinor Lax342547.FractionalColoring

/--
---
conclusion: Lax342547.FractionalCounterexample.arbitrarily_large_fractional_counterexample
assumptions:
  - Lax342547.Counterexample.arbitrarily_large_small_connected_matching
---
Theorem 1.1 supplies the graph. Apply the matching-minor bound and the two
proved fractional-coloring inequalities. The only remaining hypothesis
is the construction asserted by Theorem 1.1.
-/
theorem arbitrarily_large_fractional_counterexample (lowerBound : ℕ) :
    ∃ m : ℕ, lowerBound ≤ m ∧ 5 ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧
      (hadwigerNumber G : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧
      26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
      (m : ℝ) / 2 ≤ fractionalChromaticNumber G ∧
      fractionalChromaticNumber G ≤ (G.chromaticNumber.toNat : ℝ) := by
  obtain ⟨m, hm, G, hα, hc⟩ :=
    Lax342547.Counterexample.arbitrarily_large_small_connected_matching (max lowerBound 5)
  have hm5 : 5 ≤ m := (le_max_right _ _).trans hm
  have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm5
  have hcR : 100 * (connectedMatchingNumber G : ℝ) < m := by exact_mod_cast hc
  have hminor : 3 * (hadwigerNumber G : ℝ) ≤
      (m : ℝ) + 4 * (connectedMatchingNumber G : ℝ) + 2 := by
    have h := HadwigerMatching.hadwiger_matching_bound G
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  refine ⟨m, (le_max_left _ _).trans hm, hm5, G, hα, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · simpa using FractionalColoring.fractional_chromatic_lower_bound G hα
  · exact FractionalColoring.fractional_chromatic_le_chromatic G

end Lax342547Proofs.FractionalCounterexample
