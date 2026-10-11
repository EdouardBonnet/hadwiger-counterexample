import Lax342547.AdaptiveSets

/-!
---
title: Union over adaptive component covers
type: lemma
---
All disjoint exposed and tested index sets have the finite union bound four to the number of coordinates times the cover mass to the number of tests.
-/

namespace Lax342547.AdaptiveUnion

open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

axiom adaptive_cover_union {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (A : ∀ E : Finset ι, (E → Ω) → Ω → Prop) (p : ℝ) (k : ℕ)
    (hμ : Probability μ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hA : ∀ E exposed, cellMass μ (A E exposed) ≤ p) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∃ E J : Finset ι, Disjoint E J ∧ k ≤ J.card ∧
        ∀ j ∈ J, A E (fun e => sample e.val) (sample j)) ≤
      (4 : ℝ)^Fintype.card ι*p^k

end Lax342547.AdaptiveUnion
