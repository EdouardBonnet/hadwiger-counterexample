import Lax342547.ConnectedMatching
import Lax342547.CliqueMinor
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
---
title: A counterexample to Hadwiger's conjecture
type: theorem
---
Theorem 1.1 asserts that graphs of arbitrarily large order $m$ have
independence number at most two and connected-matching number less than
$m/100$. Together with Proposition 3.5, this gives graphs of arbitrarily
large order with $h(G)<\chi(G)$.

The existence assertion is the construction to be proved; the counting
inequality alone does not establish it.
-/

namespace Lax342547.Counterexample

open ConnectedMatching CliqueMinor

/-- Theorem 1.1, with the strict matching bound expressed in natural numbers. -/
axiom arbitrarily_large_small_connected_matching (lowerBound : ℕ) :
    ∃ m : ℕ, lowerBound ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ 100 * connectedMatchingNumber G < m

/-- The ordinary coloring consequence of Theorem 1.1. -/
axiom arbitrarily_large_hadwiger_counterexample (lowerBound : ℕ) :
    ∃ m : ℕ, lowerBound ≤ m ∧ 5 ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧ hadwigerNumber G < G.chromaticNumber.toNat

end Lax342547.Counterexample
