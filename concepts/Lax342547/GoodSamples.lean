import Lax342547.DisjointSampling

/-!
---
title: A good sample from the explicit container budget
type: lemma
---
The vertex and disjoint pair exception tails sum over the finite container family. If their explicit total budget is less than one, a sample avoiding every terminal exception event exists.
-/

namespace Lax342547.GoodSamples

open Lax342547.RelativeEntropy Lax342547.FiniteSampling Lax342547.RetainedImages Lax342547.CellAveraging
open scoped BigOperators

noncomputable def Bad {Ω : Type} {m : ℕ} (S : Ω → Prop) (E : Ω → Ω → Prop) (k : ℕ)
    (sample : Fin m → Ω) : Prop := by
  classical
  exact k ≤ (Finset.univ.filter (fun i => S (sample i))).card ∨
    ∃ a : Fin k × Bool ↪ Fin m, ∀ j, E (sample (a (j,false))) (sample (a (j,true)))

axiom cell_mass_or {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (S T : Ω → Prop) (hρ : ∀ x, 0 ≤ ρ x) :
    cellMass ρ (fun x => S x ∨ T x) ≤ cellMass ρ S+cellMass ρ T

axiom bad_sample_bound {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (S : Ω → Prop) (E : Ω → Ω → Prop)
    (m k : ℕ) (M κ : ℝ) (hμ : Probability μ) (_hM : 0 < M) (_hκ : 0 < κ)
    (hS : cellMass μ S < 1/M) (hE : pairEventMass μ μ E < 1/κ) :
    cellMass (productLaw (fun _ : Fin m => μ)) (Bad S E k) ≤
      (m.choose k : ℝ)*(1/M)^k+(m : ℝ)^(2*k)*(1/κ)^k

axiom mass_less_one_exists_complement {Ω : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (A : Ω → Prop) (hρ : Probability ρ) (hA : cellMass ρ A < 1) : ∃ x, ¬ A x

axiom exists_good_sample {Ω J : Type} [Fintype Ω]
    (μ : Ω → ℝ) (C : Finset J) (S : J → Ω → Prop) (E : J → Ω → Ω → Prop)
    (m k : ℕ) (M κ : ℝ) (hμ : Probability μ) (hM : 0 < M) (hκ : 0 < κ)
    (hS : ∀ c ∈ C, cellMass μ (S c) < 1/M)
    (hE : ∀ c ∈ C, pairEventMass μ μ (E c) < 1/κ)
    (hbudget : (C.card : ℝ)*((m.choose k : ℝ)*(1/M)^k+(m : ℝ)^(2*k)*(1/κ)^k) < 1) :
    ∃ sample : Fin m → Ω, ∀ c ∈ C, ¬ Bad (S c) (E c) k sample

end Lax342547.GoodSamples
