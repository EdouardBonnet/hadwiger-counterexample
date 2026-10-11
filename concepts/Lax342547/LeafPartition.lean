import Lax342547.LeafExtraction
import Mathlib.Data.Finset.Union

/-!
---
title: Finite peeling into disjoint exact-pin leaves
type: lemma
---
Repeated leaf extraction partitions the retained support, leaving mass at
most delta. Every leaf retains its original mass lower bound, exact pins,
and all positive-rank relative image caps.
-/

namespace Lax342547.LeafPartition

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.LeafExtraction
open scoped ENNReal

def Partition {Ω Axis I N : Type} [DecidableEq Ω] [Fintype Axis]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Finset Ω) (δ α : ℝ≥0∞)
    (L : Finset (Finset Ω × Pin Axis I N)) : Prop :=
  (∀ z ∈ L, z.1 ⊆ R ∧ P₀.Extends z.2 ∧ (z.1 : Set Ω) ⊆ z.2.event A ∧
    δ * α ^ (z.2.rank - P₀.rank) < p.toOuterMeasure z.1 ∧ Good p A z.2 z.1 α) ∧
  (∀ z ∈ L, ∀ w ∈ L, z ≠ w → Disjoint z.1 w.1) ∧
  p.toOuterMeasure (R \ L.biUnion Prod.fst : Finset Ω) ≤ δ

axiom exists_partition {Ω Axis I N : Type}
    [DecidableEq Ω] [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Finset Ω) (hR : (R : Set Ω) ⊆ P₀.event A)
    (δ α : ℝ≥0∞) (hα₀ : α ≠ 0) (hαtop : α ≠ ⊤) :
    ∃ L : Finset (Finset Ω × Pin Axis I N), Partition p A P₀ R δ α L

end Lax342547.LeafPartition
