import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteLaws

namespace Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
noncomputable section
variable {α : Type*} [Fintype α]

/-- Individual marginal caps (mapW denotes the actual marginals) and a joint cap. -/
def pairCaps (μ : Wgt α) (m d : ℝ) (w : Wgt (α × α)) :=
  (∀ x, mapW w Prod.fst x ≤ m * μ x) ∧
  (∀ x, mapW w Prod.snd x ≤ m * μ x) ∧
  (∀ p, w p ≤ d * pairW μ μ p)

end
end Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
