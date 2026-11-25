import Lax793645.OverlapTransfer
import Lax793645.FiniteScores

/-!
---
title: Finite overlap obstruction for independently sampled leaves
type: theorem
---
For each option, suppose actual successful-query overlap has mean at most
$\delta$, and the projection, tuple-cell and tail errors have total mean
at most $\varepsilon$. Then a surrogate overlap of at least $a>0$ occurs
for some usable option with probability at most
$|\mathcal O|(\delta+\varepsilon)/a^2$.

Both actual and surrogate densities may depend on both leaves, whose law is
the independent product $\alpha\otimes\beta$. Filters are already included
in the subprobability masses. Adaptive partitions supply the bounded-size
common partition; histogram control and weak product comparison supply the
error bounds. Letting these bounds be arbitrarily small gives the
fixed-threshold replacement for the common-limit obstruction.
-/

namespace Lax793645.FiniteObstruction
noncomputable section
open FiniteProbability

def error {A C : Type} [Fintype A] [Fintype C]
    (μ : Weight A) (p : A → C) (R : ℝ) (f g x y : Weight A) : ℝ :=
  |projectionError μ (clip R μ x) (clip R μ y) p| +
    ((cellError μ p f x + tail R μ x) + (cellError μ p g y + tail R μ y))

axiom threshold_bound {I J O A C : Type}
    [Fintype I] [Fintype J] [Fintype O] [Fintype A] [Fintype C]
    (α : Weight I) (β : Weight J) (μ : Weight A)
    (hα : Probability α) (hβ : Probability β) (hμ : Probability μ)
    (usable : O → Prop) (p : O → A → C) (R δ ε a : ℝ)
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (ha : 0 < a)
    (f g x y : O → I × J → Weight A)
    (hf : ∀ o z, bounded (f o z)) (hg : ∀ o z, bounded (g o z))
    (hx : ∀ o z, Subprobability (x o z)) (hy : ∀ o z, Subprobability (y o z))
    (hxs : ∀ o z, dominatedSupport (x o z) μ)
    (hys : ∀ o z, dominatedSupport (y o z) μ)
    (hactual : ∀ o, usable o → expectation (product α β) (fun z =>
      inner μ (density μ (x o z)) (density μ (y o z))) ≤ δ)
    (herror : ∀ o, usable o → expectation (product α β) (fun z =>
      error μ (p o) R (f o z) (g o z) (x o z) (y o z)) ≤ ε) :
    mass (product α β) (fun z => ∃ o, usable o ∧ a ≤ inner μ (f o z) (g o z)) ≤
      (Fintype.card O : ℝ) * ((δ + ε) / a ^ 2)

end
end Lax793645.FiniteObstruction
