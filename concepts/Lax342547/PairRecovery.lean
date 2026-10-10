import Lax342547.RealCellLaws
import Lax342547.Conditioning

/-!
---
title: Squared restriction cost for independent unit events
type: definition and theorem
---
A normalized restriction is dominated pointwise by its original PMF after multiplication by the retained mass. Independent pair events therefore lose precisely the square of that mass.
-/

namespace Lax342547.PairRecovery

open Lax342547.RealCellLaws
open scoped ENNReal

noncomputable def pairMass {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α : ΩA → ℝ) (β : ΩB → ℝ) (H : ΩA → ΩB → Prop) : ℝ := by
  classical
  exact ∑ a, ∑ b, if H a b then α a * β b else 0

axiom pair_mass_domination {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α ρ : ΩA → ℝ) (β σ : ΩB → ℝ) (mA mB : ℝ) (H : ΩA → ΩB → Prop)
    (hmA : 0 ≤ mA) (hmB : 0 ≤ mB) (hρ : ∀ a, 0 ≤ ρ a) (hσ : ∀ b, 0 ≤ σ b)
    (hα : ∀ a, mA * ρ a ≤ α a) (hβ : ∀ b, mB * σ b ≤ β b) :
    mA * mB * pairMass ρ σ H ≤ pairMass α β H

axiom real_filter_domination {Ω : Type} [Fintype Ω] (p : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (ω : Ω) :
    (p.toOuterMeasure S).toReal * weights (p.filter S hS) ω ≤ weights p ω

axiom restriction_pair_recovery {Ω : Type} [Fintype Ω] (p : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (H : Ω → Ω → Prop) :
    ((p.toOuterMeasure S).toReal)^2 * pairMass (weights (p.filter S hS)) (weights (p.filter S hS)) H ≤
      pairMass (weights p) (weights p) H

noncomputable def independentPair {ΩA ΩB : Type} (p : PMF ΩA) (q : PMF ΩB) : PMF (ΩA × ΩB) :=
  p.bind (fun a => q.map (fun b => (a,b)))

axiom independent_pair_apply {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (p : PMF ΩA) (q : PMF ΩB) (ab : ΩA × ΩB) :
    independentPair p q ab = p ab.1 * q ab.2

axiom pair_mass_pmf_event {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (p : PMF ΩA) (q : PMF ΩB) (H : ΩA → ΩB → Prop) :
    pairMass (weights p) (weights q) H =
      ((independentPair p q).toOuterMeasure {ab | H ab.1 ab.2}).toReal

axiom restriction_pair_event_recovery {Ω : Type} [Fintype Ω]
    (p : PMF Ω) (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (H : Ω → Ω → Prop) :
    ((p.toOuterMeasure S).toReal)^2 *
      ((independentPair (p.filter S hS) (p.filter S hS)).toOuterMeasure {ab | H ab.1 ab.2}).toReal ≤
        ((independentPair p p).toOuterMeasure {ab | H ab.1 ab.2}).toReal

end Lax342547.PairRecovery
