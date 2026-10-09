import Lax342547.SplitTrimming
import Lax342547.BoundedPeeling
import Mathlib.Algebra.Order.Floor.Ring

/-!
---
title: Fresh peeling after restrictions and deliberate extra pins
type: definition and theorem
---
Every retained metadata fiber carries its old pins and all new prescribed
images. Its absolute density pays both preceding normalizations. A fresh
peeling fits inside the paper's final total pin budget.
-/

namespace Lax342547.SecondPeeling

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.MetadataPins
open Lax342547.LeafPartition Lax342547.BoundedPeeling
open scoped ENNReal

def startCost (D : ℝ) (K₁ u : ℕ) : ℝ := D + K₁ + u + 5

noncomputable def newBudget (D ζ : ℝ) (K₁ u : ℕ) : ℕ :=
  ⌈4 * (startCost D K₁ u + 1) / ζ⌉₊

noncomputable def finalBudget (D ζ : ℝ) (K₁ u : ℕ) : ℕ :=
  ⌈10 * (D + K₁ + u + 10) / ζ⌉₊

noncomputable def supportFinset {Ω : Type} [Fintype Ω] (p : PMF Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun o => o ∈ p.support)

def RepeeledPart {Ω J Axis I N : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Axis] [Fintype N]
    (q μ : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (choice : Ω → J) (U : J → Axis → Submodule Binary (I → Binary))
    (D ζ : ℝ) (K₁ u : ℕ) (k : Key N U) : Prop :=
  ∃ hkSupport : ∃ o ∈ {o | record A choice U o = k}, o ∈ q.support,
  let Q := q.filter {o | record A choice U o = k} hkSupport
  ∃ P : Pin Axis I N, ∃ L : Finset (Finset Ω × Pin Axis I N),
    P₀.Extends P ∧ (pin k).Extends P ∧ P.rank ≤ K₁ + u ∧
    Partition Q A P (supportFinset Q)
      ((2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)))
      ((2 : ℝ≥0∞) ^ (-((1 - ζ) * Fintype.card N))) L ∧
    q.toOuterMeasure (supportFinset Q \ L.biUnion Prod.fst) ≤
      (2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)) *
        q.toOuterMeasure {o | record A choice U o = k} ∧
    ∀ z ∈ L, z.2.rank ≤ finalBudget D ζ K₁ u ∧
      LawBound Q μ A z.2 z.1
        ((2 : ℝ≥0∞) ^ (-((1 - ζ) * Fintype.card N)))
        ((2 : ℝ≥0∞) ^ ((startCost D K₁ u + newBudget D ζ K₁ u + 1) * Fintype.card N))

axiom final_rank_budget (D ζ : ℝ) (K₁ u : ℕ)
    (hD : 0 ≤ D) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) :
    K₁ + u + newBudget D ζ K₁ u ≤ finalBudget D ζ K₁ u

axiom second_part {Ω J Axis I N : Type}
    [Fintype Ω] [DecidableEq Ω] [Fintype Axis] [Fintype I] [Fintype N]
    (p μ : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support)
    (choice : Ω → J) (U : J → Axis → Submodule Binary (I → Binary))
    (D ζ ε : ℝ) (K₁ u : ℕ)
    (hD : 0 ≤ D) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : ε ≤ ζ / 4)
    (hN : 0 < Fintype.card N) (hP : p.support ⊆ P₀.event A) (hPbudget : P₀.rank ≤ K₁)
    (hu : ∀ j, ∑ a, Module.finrank Binary (U j a) ≤ u)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)) ≤ p.toOuterMeasure S)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ ((D + K₁ + 1) * Fintype.card N) * μ o)
    (hreference : ∀ P : Pin Axis I N, μ.toOuterMeasure (P.event A) ≤
      (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * Fintype.card N)))
    (k : Key N U)
    (hk : (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N)) ≤
      (p.filter S hS).toOuterMeasure {o | record A choice U o = k}) :
    RepeeledPart (p.filter S hS) μ A P₀ choice U D ζ K₁ u k

end Lax342547.SecondPeeling
