import Lax342547.ExactPins
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
---
title: Extracting a leaf with all remaining exact-image caps
type: definition and theorem
---
Among pin extensions that retain enough of the original mass, choose one
of maximal rank. A remaining unusually likely positive-rank constraint
would produce a larger candidate, so every such image test obeys the cap.
-/

namespace Lax342547.LeafExtraction

open Lax342547.MomentSpace Lax342547.ExactPins
open scoped ENNReal

def Good {Ω Axis I N : Type} [Fintype Axis] (p : PMF Ω)
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) (S : Set Ω) (α : ℝ≥0∞) : Prop :=
  ∀ Q : Pin Axis I N, 1 ≤ P.relativeRank Q →
    p.toOuterMeasure (S ∩ Q.event A) ≤ α ^ (P.relativeRank Q) * p.toOuterMeasure S

axiom exists_leaf {Ω Axis I N : Type}
    [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Set Ω) (hR : R ⊆ P₀.event A)
    (δ α : ℝ≥0∞) (hα₀ : α ≠ 0) (hαtop : α ≠ ⊤) (hmass : δ < p.toOuterMeasure R) :
    ∃ P : Pin Axis I N, P₀.Extends P ∧
      δ * α ^ (P.rank - P₀.rank) < p.toOuterMeasure (R ∩ P.event A) ∧
      Good p A P (R ∩ P.event A) α

end Lax342547.LeafExtraction
