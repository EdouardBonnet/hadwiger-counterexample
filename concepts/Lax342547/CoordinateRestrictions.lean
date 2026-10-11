import Lax342547.FiniteSampling
import Mathlib.Logic.Equiv.Set

/-!
---
title: Independence of distinct sample positions
type: definition and theorem
---
An embedding of selected positions extends to a partition of the whole position space. Summing the unused independent coordinates proves the exact product law on the selected positions.
-/

namespace Lax342547.CoordinateRestrictions

open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open scoped BigOperators

noncomputable def complete {J ι : Type} (a : J ↪ ι) : J ⊕ {i : ι // i ∉ Set.range a} ≃ ι := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective a a.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range a))

axiom complete_left {J ι : Type} (a : J ↪ ι) (j : J) : complete a (.inl j) = a j

axiom sum_restriction {J K Ω : Type} [Fintype J] [Fintype K] [Fintype Ω]
    [DecidableEq J] [DecidableEq K]
    (μ : Ω → ℝ) (A : (J → Ω) → Prop) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : J ⊕ K => μ)) (fun sample => A (fun j => sample (.inl j))) =
      cellMass (productLaw (fun _ : J => μ)) A

axiom embedding_restriction {J ι Ω : Type} [Fintype J] [Fintype ι] [Fintype Ω]
    [DecidableEq J] [DecidableEq ι]
    (μ : Ω → ℝ) (a : J ↪ ι) (A : (J → Ω) → Prop) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ)) (fun sample => A (fun j => sample (a j))) =
      cellMass (productLaw (fun _ : J => μ)) A

end Lax342547.CoordinateRestrictions
