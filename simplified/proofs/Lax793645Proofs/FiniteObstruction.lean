import Lax793645.FiniteObstruction
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteLaws

namespace Lax793645Proofs.FiniteObstruction
open Lax793645.FiniteProbability Lax793645.FiniteObstruction
open Upstream.OAI.HadwigerCounterexample

/--
---
conclusion: Lax793645.FiniteObstruction.threshold_bound
---
-/
theorem threshold_bound {I J O A C : Type}
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
      inner μ (Lax793645.FiniteProbability.density μ (x o z))
        (Lax793645.FiniteProbability.density μ (y o z))) ≤ δ)
    (herror : ∀ o, usable o → expectation (product α β) (fun z =>
      error μ (p o) R (f o z) (g o z) (x o z) (y o z)) ≤ ε) :
    mass (product α β) (fun z => ∃ o, usable o ∧ a ≤ inner μ (f o z) (g o z)) ≤
      (Fintype.card O : ℝ) * ((δ + ε) / a ^ 2) := by
  let E (o : O) (z : I × J) :=
    inner μ (Lax793645.FiniteProbability.density μ (x o z))
      (Lax793645.FiniteProbability.density μ (y o z)) +
      error μ (p o) R (f o z) (g o z) (x o z) (y o z)
  apply Lax793645.FiniteScores.squared_score_probability α β hα hβ usable
    (fun o z => inner μ (f o z) (g o z)) E (δ + ε) a (add_nonneg hδ hε) ha
  · intro o _ z
    have h := Lax793645.OverlapTransfer.finite_transfer μ hμ (p o) R hR
      (f o z) (g o z) (x o z) (y o z) (hf o z) (hg o z)
      (hx o z) (hy o z) (hxs o z) (hys o z)
    simpa only [E, error, add_assoc] using h
  · intro o ho
    change avg (product α β) (fun z => _ + _) ≤ _
    rw [avg_add]
    exact add_le_add (hactual o ho) (herror o ho)

end Lax793645Proofs.FiniteObstruction
