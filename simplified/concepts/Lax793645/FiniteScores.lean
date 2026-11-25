import Lax793645.FiniteProbability

/-!
---
title: Suppression of options above a fixed overlap threshold
type: lemma
---
If each of finitely many nonnegative option scores has expectation at most
$\varepsilon$, the probability that a usable option has score at least
$a>0$ is at most $|\mathcal O|\varepsilon/a$. The same estimate with
$\delta/a^2$ applies when the squared score is bounded by an error of mean
at most $\delta$. Applied after finite overlap transfer, this is the finite
replacement for the limiting overlap obstruction. Scores retain all flag
and filter masses.
-/

namespace Lax793645.FiniteScores
open FiniteProbability

axiom large_score_probability {X O : Type} [Fintype X] [Fintype O]
    (μ : Weight X) (hμ : Probability μ) (usable : O → Prop)
    (score : O → X → ℝ) (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a)
    (hn : ∀ o, usable o → ∀ x, 0 ≤ score o x)
    (he : ∀ o, usable o → expectation μ (score o) ≤ ε) :
    mass μ (fun x => ∃ o, usable o ∧ a ≤ score o x) ≤
      (Fintype.card O : ℝ) * (ε / a)

axiom squared_score_probability {I J O : Type} [Fintype I] [Fintype J] [Fintype O]
    (α : Weight I) (β : Weight J) (hα : Probability α) (hβ : Probability β)
    (usable : O → Prop) (score error : O → I × J → ℝ) (δ a : ℝ)
    (hδ : 0 ≤ δ) (ha : 0 < a)
    (hm : ∀ o, usable o → ∀ z, score o z ^ 2 ≤ error o z)
    (he : ∀ o, usable o → expectation (product α β) (error o) ≤ δ) :
    mass (product α β) (fun z => ∃ o, usable o ∧ a ≤ score o z) ≤
      (Fintype.card O : ℝ) * (δ / a ^ 2)

end Lax793645.FiniteScores
