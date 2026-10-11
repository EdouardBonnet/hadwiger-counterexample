import Lax342547.ContainerLaws
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
---
title: Finite independent sampling and vertex exception tails
type: lemma
---
Finite product weights form a probability law. Cylinder events factor over sample positions, and a subset union bound gives the binomial estimate for too many positions in a raw vertex exception.
-/

namespace Lax342547.FiniteSampling

open Lax342547.RelativeEntropy Lax342547.RetainedImages
open scoped BigOperators

noncomputable def productLaw {ι Ω : Type} [Fintype ι] (μ : ι → Ω → ℝ) (sample : ι → Ω) : ℝ :=
  ∏ i, μ i (sample i)

axiom product_probability {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : ι → Ω → ℝ) (hμ : ∀ i, Probability (μ i)) : Probability (productLaw μ)

axiom cylinder_probability {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : ι → Ω → ℝ) (A : ι → Ω → Prop) :
    cellMass (productLaw μ) (fun sample => ∀ i, A i (sample i)) = ∏ i, cellMass (μ i) (A i)

axiom coordinate_set_probability {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (T : Finset ι) (S : Ω → Prop) (hμ : Probability μ) :
    cellMass (productLaw (fun _ : ι => μ)) (fun sample => ∀ i ∈ T, S (sample i)) =
      (cellMass μ S)^T.card

axiom cell_mass_mono {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (S T : Ω → Prop) (hρ : ∀ x, 0 ≤ ρ x) (hST : ∀ x, S x → T x) :
    cellMass ρ S ≤ cellMass ρ T

axiom cell_mass_union_bound {Ω J : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (A : J → Ω → Prop) (T : Finset J) (hρ : ∀ x, 0 ≤ ρ x) :
    cellMass ρ (fun x => ∃ j ∈ T, A j x) ≤ ∑ j ∈ T, cellMass ρ (A j)

axiom exceptional_positions_bound {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]
    (μ : Ω → ℝ) (S : Ω → Prop) (k : ℕ) (hμ : Probability μ) : by
      classical
      exact cellMass (productLaw (fun _ : ι => μ))
          (fun sample => k ≤ (Finset.univ.filter (fun i => S (sample i))).card) ≤
        (Fintype.card ι).choose k*(cellMass μ S)^k

end Lax342547.FiniteSampling
