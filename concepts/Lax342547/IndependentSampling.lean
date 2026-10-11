import Lax342547.SequentialTests
import Lax342547.GreedySpaces
import Lax342547.FiniteSampling
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Data.Fin.Tuple.Basic

/-!
---
title: Greedy independent failure samples
type: definition and theorem
---
Actual sequential failure tests produce independent pin spaces and retain a uniform amplified lower probability.
-/

namespace Lax342547.IndependentSampling

open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages Lax342547.FiniteSampling
open scoped BigOperators

axiom accepted_spaces_independent {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    (U : Ω → Submodule K V) (F : Ω → Prop) (n : ℕ) (s : Fin n → Ω)
    (hs : Lax342547.SequentialTests.accepts
      (fun j t x => F x ∧ Disjoint (U x) (⨆ i : Fin j,U (t i))) n s) :
    iSupIndep (fun i => U (s i))

axiom greedy_failure_lower_probability {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Fintype Ω] (U : Ω → Submodule K V) (μ : Ω → ℝ) (F : Ω → Prop)
    (η δ : ℝ) (n : ℕ) (hμ : Probability μ) (hgap : δ ≤ η)
    (hF : η ≤ cellMass μ F)
    (havoid : ∀ j,j < n → ∀ t : Fin j → Ω,
      cellMass μ (fun x => ¬ Disjoint (U x) (⨆ i : Fin j,U (t i))) ≤ δ) :
    (η-δ)^n ≤ cellMass (productLaw (fun _ : Fin n => μ))
      (fun s => Lax342547.SequentialTests.accepts
        (fun j t x => F x ∧ Disjoint (U x) (⨆ i : Fin j,U (t i))) n s)

end Lax342547.IndependentSampling
