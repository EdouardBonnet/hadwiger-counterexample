import Lax342547.CliqueMinor
import Lax342547.FractionalColoring

/-!
---
title: The fractional-coloring counterexample
type: theorem
---
Corollary 1.2 asserts that there are graphs of arbitrarily large order $m$
with independence number at most two and
$h(G)<26m/75+2/3<m/2\le\chi_f(G)\le\chi(G)$.
Here $h(G)$ refers to ordinary clique minors.
-/

namespace Lax342547.FractionalCounterexample

open CliqueMinor FractionalColoring

axiom arbitrarily_large_fractional_counterexample (lowerBound : ℕ) :
    ∃ m : ℕ, lowerBound ≤ m ∧ 5 ≤ m ∧ ∃ G : SimpleGraph (Fin m),
      G.indepNum ≤ 2 ∧
      (hadwigerNumber G : ℝ) < 26 * (m : ℝ) / 75 + 2 / 3 ∧
      26 * (m : ℝ) / 75 + 2 / 3 < (m : ℝ) / 2 ∧
      (m : ℝ) / 2 ≤ fractionalChromaticNumber G ∧
      fractionalChromaticNumber G ≤ (G.chromaticNumber.toNat : ℝ)

end Lax342547.FractionalCounterexample
