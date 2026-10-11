import Lax342547.AdaptiveSampling

/-!
---
title: Adaptive sampling on disjoint coordinate sets
type: definition and theorem
---
Arbitrary disjoint exposed and tested index sets inherit the conditional product-law power bound through an explicit sum embedding.
-/

namespace Lax342547.AdaptiveSets

open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

axiom embedding_adaptive_bound {E J ι Ω : Type} [Fintype E] [Fintype J] [Fintype ι] [Fintype Ω]
    [DecidableEq E] [DecidableEq J] [DecidableEq ι]
    (μ : Ω → ℝ) (a : E ⊕ J ↪ ι) (A : (E → Ω) → Ω → Prop) (p : ℝ)
    (hμ : Probability μ) (hA : ∀ exposed, cellMass μ (A exposed) ≤ p) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∀ j, A (fun e => sample (a (.inl e))) (sample (a (.inr j)))) ≤ p^Fintype.card J

noncomputable def disjointEmbedding {ι : Type} [DecidableEq ι] (E J : Finset ι)
    (h : Disjoint E J) : E ⊕ J ↪ ι :=
  { toFun := Sum.elim Subtype.val Subtype.val
    inj' := by
      intro x y hxy
      cases x with
      | inl e =>
        cases y with
        | inl e' => exact congrArg Sum.inl (Subtype.ext hxy)
        | inr j =>
          dsimp at hxy
          exact False.elim ((Finset.disjoint_left.mp h) e.property (hxy.symm ▸ j.property))
      | inr j =>
        cases y with
        | inl e =>
          dsimp at hxy
          exact False.elim ((Finset.disjoint_left.mp h) e.property (hxy ▸ j.property))
        | inr j' => exact congrArg Sum.inr (Subtype.ext hxy) }

axiom disjoint_adaptive_bound {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (E J : Finset ι) (h : Disjoint E J)
    (A : (E → Ω) → Ω → Prop) (p : ℝ)
    (hμ : Probability μ) (hA : ∀ exposed, cellMass μ (A exposed) ≤ p) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∀ j ∈ J, A (fun e => sample e.val) (sample j)) ≤ p^J.card

end Lax342547.AdaptiveSets
