import Lax793645.FiniteScores
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteLaws

namespace Lax793645Proofs.FiniteScores
open Lax793645.FiniteProbability
open Upstream.OAI.HadwigerCounterexample
open scoped BigOperators

/--
---
conclusion: Lax793645.FiniteScores.large_score_probability
---
-/
theorem large_score_probability {X O : Type} [Fintype X] [Fintype O]
    (μ : Weight X) (hμ : Probability μ) (usable : O → Prop)
    (score : O → X → ℝ) (ε a : ℝ) (hε : 0 ≤ ε) (ha : 0 < a)
    (hn : ∀ o, usable o → ∀ x, 0 ≤ score o x)
    (he : ∀ o, usable o → expectation μ (score o) ≤ ε) :
    mass μ (fun x => ∃ o, usable o ∧ a ≤ score o x) ≤
      (Fintype.card O : ℝ) * (ε / a) := by
  classical
  have hp (o : O) : pr μ (fun x => usable o ∧ a ≤ score o x) ≤ ε / a := by
    by_cases ho : usable o
    · simp only [ho, true_and]
      apply (le_div_iff₀ ha).mpr
      rw [mul_comm]
      exact (le_avg_markov hμ.1 (hn o ho) a).trans (he o ho)
    simp only [ho, false_and, pr_false]
    exact div_nonneg hε ha.le
  exact (pr_exists_le hμ.1 _).trans ((Finset.sum_le_sum (fun o _ => hp o)).trans_eq
    (by simp))

/--
---
conclusion: Lax793645.FiniteScores.squared_score_probability
---
-/
theorem squared_score_probability {I J O : Type} [Fintype I] [Fintype J] [Fintype O]
    (α : Weight I) (β : Weight J) (hα : Probability α) (hβ : Probability β)
    (usable : O → Prop) (score error : O → I × J → ℝ) (δ a : ℝ)
    (hδ : 0 ≤ δ) (ha : 0 < a)
    (hm : ∀ o, usable o → ∀ z, score o z ^ 2 ≤ error o z)
    (he : ∀ o, usable o → expectation (product α β) (error o) ≤ δ) :
    mass (product α β) (fun z => ∃ o, usable o ∧ a ≤ score o z) ≤
      (Fintype.card O : ℝ) * (δ / a ^ 2) := by
  have hw : IsLaw (product α β) := pairW_law ⟨hα.1, hα.2⟩ ⟨hβ.1, hβ.2⟩
  have bound := Lax793645.FiniteScores.large_score_probability (product α β)
    ⟨hw.nz, hw.total⟩ usable (fun o z => score o z ^ 2) δ (a ^ 2) hδ
    (sq_pos_of_pos ha) (fun _ _ _ => sq_nonneg _)
    (fun o ho => (avg_mono hw.nz (hm o ho)).trans (he o ho))
  apply (pr_mono hw.nz (fun z hz => ?_)).trans bound
  obtain ⟨o, ho, hs⟩ := hz
  exact ⟨o, ho, pow_le_pow_left₀ ha.le hs 2⟩

end Lax793645Proofs.FiniteScores
