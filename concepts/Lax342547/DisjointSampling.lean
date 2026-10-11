import Lax342547.CoordinateRestrictions
import Lax342547.CellAveraging
import Mathlib.Logic.Equiv.Prod

/-!
---
title: Disjoint pair exception tails
type: lemma
---
Distinct selected sample positions retain their product law, and grouping them into ordered pairs proves the exact power of the raw pair-exception mass. Union over all position embeddings gives the m^(2k) counting bound.
-/

namespace Lax342547.DisjointSampling

open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages
open Lax342547.CellAveraging
open scoped BigOperators

noncomputable def pairSamples {J Ω : Type} : (J → Ω × Ω) ≃ (J × Bool → Ω) :=
  (Equiv.piCongrRight (fun _ : J => (Equiv.boolArrowEquivProd Ω).symm)).trans
    (Equiv.curry J Bool Ω).symm

axiom pair_samples_left {J Ω : Type} (sample : J → Ω × Ω) (j : J) :
    pairSamples sample (j,false) = (sample j).1

axiom pair_samples_right {J Ω : Type} (sample : J → Ω × Ω) (j : J) :
    pairSamples sample (j,true) = (sample j).2

axiom paired_product_probability {J Ω : Type} [Fintype J] [Fintype Ω] [DecidableEq J]
    (μ : Ω → ℝ) (E : Ω → Ω → Prop) :
    cellMass (productLaw (fun _ : J × Bool => μ))
      (fun sample => ∀ j, E (sample (j,false)) (sample (j,true))) =
        (pairEventMass μ μ E)^Fintype.card J

axiom disjoint_pair_probability {J ι Ω : Type} [Fintype J] [Fintype ι] [Fintype Ω]
    [DecidableEq J] [DecidableEq ι]
    (μ : Ω → ℝ) (a : J × Bool ↪ ι) (E : Ω → Ω → Prop) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∀ j, E (sample (a (j,false))) (sample (a (j,true)))) =
        (pairEventMass μ μ E)^Fintype.card J

axiom disjoint_pair_exception_bound {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (E : Ω → Ω → Prop) (k : ℕ) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ))
      (fun sample => ∃ a : Fin k × Bool ↪ ι,
        ∀ j, E (sample (a (j,false))) (sample (a (j,true)))) ≤
      (Fintype.card ι)^(2*k)*(pairEventMass μ μ E)^k

end Lax342547.DisjointSampling
