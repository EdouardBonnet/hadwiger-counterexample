import Lax793645.ResidualRegularity
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ResidualRegularity

namespace Lax793645Proofs.ResidualRegularity
open Lax793645.FiniteProbability Lax793645.ResidualRegularity

/--
---
conclusion: Lax793645.ResidualRegularity.common_partition
---
-/
theorem common_partition (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ bound : ℕ, ∀ (A I : Type) [Fintype A] [Fintype I]
      (α : Weight I) (μ : Weight A) (f : I → Weight A),
      Probability α → Probability μ → (∀ i x, |f i x| ≤ R) →
      ∃ k : ℕ, k ≤ bound ∧ ∃ p : A → Fin k,
        ∀ h : Weight A, (∀ x, |h x| ≤ 1) →
          expectation α (fun i => |inner μ (fun x => f i x - project μ p (f i) x) h|) ≤ ε := by
  obtain ⟨k, hk⟩ := Upstream.OAI.HadwigerCounterexample.erosive_implementation R ε hR hε
  refine ⟨k, fun A I _ _ α μ f hα hμ hf => ?_⟩
  exact hk A I α μ f ⟨hα.1, hα.2⟩ ⟨hμ.1, hμ.2⟩ hf

end Lax793645Proofs.ResidualRegularity
