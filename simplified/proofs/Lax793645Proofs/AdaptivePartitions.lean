import Lax793645.AdaptivePartitions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.CommonPartitions

namespace Lax793645Proofs.AdaptivePartitions
open Lax793645.FiniteProbability Lax793645.AdaptivePartitions

/--
---
conclusion: Lax793645.AdaptivePartitions.common_partition
---
-/
theorem common_partition (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℕ, ∃ bound : ℕ,
      ∀ (I J A : Type) [Fintype I] [Fintype J] [Fintype A]
        (α : Weight I) (β : Weight J) (μ : Weight A),
        Probability α → Probability β → Probability μ →
        ∀ (P : I → Weight A → Prop) (Q : J → Weight A → Prop),
          (∀ i, HasNet (P i) r δ) → (∀ j, HasNet (Q j) r δ) →
          ∃ k : ℕ, k ≤ bound ∧ ∃ p : A → Fin k,
            ∀ f g : I × J → Weight A,
              (∀ z, P z.1 (f z)) → (∀ z, Q z.2 (g z)) →
              expectation (product α β) (fun z =>
                |projectionError μ (clip R μ (f z)) (clip R μ (g z)) p|) ≤ ε := by
  obtain ⟨δ, hd, hk⟩ := Upstream.OAI.HadwigerCounterexample.global_net_implementation R ε hR hε
  refine ⟨δ, hd, fun r => ?_⟩
  obtain ⟨l, hl⟩ := hk r
  refine ⟨l, fun I J A _ _ _ α β μ hα hβ hμ P Q hp hq => ?_⟩
  exact hl I J A α β μ ⟨hα.1, hα.2⟩ ⟨hβ.1, hβ.2⟩ ⟨hμ.1, hμ.2⟩ P Q hp hq

end Lax793645Proofs.AdaptivePartitions
