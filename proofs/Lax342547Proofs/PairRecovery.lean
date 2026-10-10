import Lax342547.PairRecovery
import Lax342547Proofs.RealCellLaws
import Lax342547Proofs.Conditioning

namespace Lax342547Proofs.PairRecovery
open Lax342547.PairRecovery

set_option backward.isDefEq.respectTransparency false
open Lax342547.RealCellLaws
open scoped ENNReal

/--
---
conclusion: Lax342547.PairRecovery.pair_mass_domination
---
-/
theorem pair_mass_domination {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (α ρ : ΩA → ℝ) (β σ : ΩB → ℝ) (mA mB : ℝ) (H : ΩA → ΩB → Prop)
    (hmA : 0 ≤ mA) (hmB : 0 ≤ mB) (hρ : ∀ a, 0 ≤ ρ a) (hσ : ∀ b, 0 ≤ σ b)
    (hα : ∀ a, mA * ρ a ≤ α a) (hβ : ∀ b, mB * σ b ≤ β b) :
    mA * mB * pairMass ρ σ H ≤ pairMass α β H := by
  classical
  unfold pairMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  by_cases hh : H a b
  · simp only [if_pos hh]
    have h := mul_le_mul (hα a) (hβ b) (mul_nonneg hmB (hσ b))
      ((mul_nonneg hmA (hρ a)).trans (hα a))
    convert h using 1
    ring
  · simp [hh]

/--
---
conclusion: Lax342547.PairRecovery.real_filter_domination
---
-/
theorem real_filter_domination {Ω : Type} [Fintype Ω] (p : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (ω : Ω) :
    (p.toOuterMeasure S).toReal * weights (p.filter S hS) ω ≤ weights p ω := by
  classical
  have h := congrArg ENNReal.toReal (Lax342547Proofs.Conditioning.weighted_filter p S hS ω)
  rw [ENNReal.toReal_mul] at h
  unfold weights
  rw [h]
  by_cases hω : ω ∈ S
  · simp [Set.indicator, hω]
  · simp [Set.indicator, hω, ENNReal.toReal_nonneg]

/--
---
conclusion: Lax342547.PairRecovery.restriction_pair_recovery
---
-/
theorem restriction_pair_recovery {Ω : Type} [Fintype Ω] (p : PMF Ω) (S : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support) (H : Ω → Ω → Prop) :
    ((p.toOuterMeasure S).toReal)^2 * pairMass (weights (p.filter S hS)) (weights (p.filter S hS)) H ≤
      pairMass (weights p) (weights p) H := by
  simpa only [pow_two] using pair_mass_domination (weights p) (weights (p.filter S hS))
    (weights p) (weights (p.filter S hS)) (p.toOuterMeasure S).toReal (p.toOuterMeasure S).toReal H
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    (Lax342547Proofs.RealCellLaws.weights_nonneg _) (Lax342547Proofs.RealCellLaws.weights_nonneg _)
    (real_filter_domination p S hS) (real_filter_domination p S hS)

/--
---
conclusion: Lax342547.PairRecovery.independent_pair_apply
---
-/
theorem independent_pair_apply {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (p : PMF ΩA) (q : PMF ΩB) (ab : ΩA × ΩB) :
    independentPair p q ab = p ab.1 * q ab.2 := by
  classical
  rcases ab with ⟨a,b⟩
  unfold independentPair
  simp only [PMF.bind_apply, PMF.map_apply, tsum_fintype, Prod.mk.injEq]
  simp [mul_ite, ite_and]

/--
---
conclusion: Lax342547.PairRecovery.pair_mass_pmf_event
---
-/
theorem pair_mass_pmf_event {ΩA ΩB : Type} [Fintype ΩA] [Fintype ΩB]
    (p : PMF ΩA) (q : PMF ΩB) (H : ΩA → ΩB → Prop) :
    pairMass (weights p) (weights q) H =
      ((independentPair p q).toOuterMeasure {ab | H ab.1 ab.2}).toReal := by
  classical
  rw [← Lax342547Proofs.RealCellLaws.event_mass]
  unfold Lax342547.RetainedImages.cellMass pairMass weights
  rw [Fintype.sum_prod_type]
  simp only [independent_pair_apply, ENNReal.toReal_mul]

/--
---
conclusion: Lax342547.PairRecovery.restriction_pair_event_recovery
---
-/
theorem restriction_pair_event_recovery {Ω : Type} [Fintype Ω]
    (p : PMF Ω) (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (H : Ω → Ω → Prop) :
    ((p.toOuterMeasure S).toReal)^2 *
      ((independentPair (p.filter S hS) (p.filter S hS)).toOuterMeasure {ab | H ab.1 ab.2}).toReal ≤
        ((independentPair p p).toOuterMeasure {ab | H ab.1 ab.2}).toReal := by
  rw [← pair_mass_pmf_event, ← pair_mass_pmf_event]
  exact restriction_pair_recovery p S hS H

end Lax342547Proofs.PairRecovery
