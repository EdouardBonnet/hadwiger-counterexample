import Lax342547.DisjointSampling

/-!
---
title: Weighted compatibility from inevitable sample pairs
type: definition and theorem
---
The product law at two distinct positions and a finite union bound turn an unavoidable compatible pair into a weighted probability lower bound.
-/

namespace Lax342547.PairPositions

open Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling Lax342547.CellAveraging
open scoped BigOperators

axiom distinct_pair_probability {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (E : Ω → Ω → Prop) (i j : ι) (hij : i ≠ j) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ)) (fun x => E (x i) (x j)) = pairEventMass μ μ E

axiom inevitable_pair_mass {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (E : Ω → Ω → Prop) (hμ : Probability μ)
    (hevery : ∀ x : ι → Ω, ∃ i j, i ≠ j ∧ E (x i) (x j)) :
    1 ≤ (Fintype.card ι : ℝ)^2*pairEventMass μ μ E

end Lax342547.PairPositions
