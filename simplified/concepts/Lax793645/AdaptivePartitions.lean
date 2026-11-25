import Lax793645.FiniteProbability

/-!
---
title: Common partitions for filters depending on both leaves
type: lemma
---
Two leaves are sampled independently. Each leaf has its own family of allowed
query masses, with a uniformly bounded finite $L^1$ net. A common partition
preserves the overlap of truncated query densities in mean absolute error.
After the partition is chosen, either density may be selected using both
leaves. Acceptance flags may then be applied without renormalizing.
-/

namespace Lax793645.AdaptivePartitions
open FiniteProbability

axiom common_partition (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
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
                |projectionError μ (clip R μ (f z)) (clip R μ (g z)) p|) ≤ ε

end Lax793645.AdaptivePartitions
