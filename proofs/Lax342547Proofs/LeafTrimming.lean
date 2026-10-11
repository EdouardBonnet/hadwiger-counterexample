import Lax342547.LeafTrimming
import Lax342547Proofs.Conditioning
import Lax342547Proofs.FiniteProbability
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lax342547.Conditioning

namespace Lax342547Proofs.LeafTrimming

open Lax342547.LeafTrimming
open scoped ENNReal

/--
---
conclusion: Lax342547.LeafTrimming.weighted_discard
---
Each discarded contribution is at most its original weight times the
threshold. The total original weight is at most one.
-/
theorem weighted_discard {J : Type} [Fintype J] (w q : J → ℝ≥0∞)
    (δ : ℝ≥0∞) (hw : ∑ j, w j ≤ 1) : discardedMass w q δ ≤ δ := by
  classical
  calc
    _ ≤ ∑ j, w j * δ := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : q j < δ
      · simp only [if_pos h]
        exact mul_le_mul_of_nonneg_left h.le zero_le
      · simp only [if_neg h]
        exact zero_le
    _ = (∑ j, w j) * δ := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hw zero_le
    _ = δ := one_mul _

/--
---
conclusion: Lax342547.LeafTrimming.restricted_discard
---
Divide the weighted discarded mass by the actual combined retained mass.
A quantitative lower bound on that mass yields the exact exponential loss.
-/
theorem restricted_discard {J : Type} [Fintype J] (w q : J → ℝ≥0∞)
    (ζ η : ℝ) (N : ℕ) (hw : ∑ j, w j ≤ 1)
    (hq : (2 : ℝ≥0∞) ^ (-(η * N)) ≤ ∑ j, w j * q j) :
    discardedMass w q ((2 : ℝ≥0∞) ^ (-(ζ * N))) / (∑ j, w j * q j) ≤
      (2 : ℝ≥0∞) ^ (-((ζ - η) * N)) := by
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (-(ζ * N)) / (2 : ℝ≥0∞) ^ (-(η * N)) :=
      ENNReal.div_le_div (Lax342547.LeafTrimming.weighted_discard w q _ hw) hq
    _ = _ := by
      rw [← ENNReal.rpow_sub _ _ (by norm_num) (by norm_num)]
      congr 1
      ring

/--
---
conclusion: Lax342547.LeafTrimming.event_after_restriction
---
The numerator is an intersection with the tested event and can only
decrease. Its normalization costs the inverse retained mass.
-/
theorem event_after_restriction {Ω : Type} [Fintype Ω] (p : PMF Ω)
    (S T : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (τ b : ℝ≥0∞)
    (hτ : τ ≤ p.toOuterMeasure S) (hb : p.toOuterMeasure T ≤ b) :
    (p.filter S hS).toOuterMeasure T ≤ b / τ := by
  rw [Lax342547.Conditioning.filter_event]
  exact ENNReal.div_le_div ((p.toOuterMeasure.mono Set.inter_subset_right).trans hb) hτ

/--
---
conclusion: Lax342547.LeafTrimming.minentropy_after_restriction
---
A surviving fraction at least 2^(-zeta N) costs at most zeta N in the
exponent. Since the tested rank is at least one, this fits the stated
loss from 1-zeta to 1-2zeta uniformly over all ranks.
-/
theorem minentropy_after_restriction {Ω : Type} [Fintype Ω] (p : PMF Ω)
    (S T : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (ζ : ℝ) (N t : ℕ)
    (hζ : 0 ≤ ζ) (ht : 1 ≤ t)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * N)) ≤ p.toOuterMeasure S)
    (hTbound : p.toOuterMeasure T ≤ (2 : ℝ≥0∞) ^ (-((1 - ζ) * t * N))) :
    (p.filter S hS).toOuterMeasure T ≤ (2 : ℝ≥0∞) ^ (-((1 - 2 * ζ) * t * N)) := by
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (-((1 - ζ) * t * N)) / (2 : ℝ≥0∞) ^ (-(ζ * N)) :=
      Lax342547.LeafTrimming.event_after_restriction p S T hS _ _ hSbound hTbound
    _ = (2 : ℝ≥0∞) ^ (-((1 - ζ) * t * N) - (-(ζ * N))) := by
      rw [ENNReal.rpow_sub _ _ (by norm_num) (by norm_num)]
    _ ≤ _ := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
      have hn : (0 : ℝ) ≤ N := by positivity
      have h := mul_nonneg (mul_nonneg hζ (sub_nonneg.mpr ht')) hn
      nlinarith)

/--
---
conclusion: Lax342547.LeafTrimming.density_after_restriction
---
The joint density constant increases by exactly the cost paid for the
retained fraction; the comparison remains with the unconditioned law.
-/
theorem density_after_restriction {Ω : Type} (p μ : PMF Ω)
    (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (C ζ : ℝ) (N : ℕ)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * N)) ≤ p.toOuterMeasure S)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ (C * N) * μ o) :
    ∀ o, (p.filter S hS) o ≤ (2 : ℝ≥0∞) ^ ((C + ζ) * N) * μ o := by
  intro o
  calc
    _ ≤ ((2 : ℝ≥0∞) ^ (C * N) / p.toOuterMeasure S) * μ o :=
      Lax342547.Conditioning.filter_density p μ S hS _ hp o
    _ ≤ ((2 : ℝ≥0∞) ^ (C * N) / (2 : ℝ≥0∞) ^ (-(ζ * N))) * μ o :=
      mul_le_mul_of_nonneg_right (ENNReal.div_le_div_left hSbound _) zero_le
    _ = _ := by
      rw [← ENNReal.rpow_sub _ _ (by norm_num) (by norm_num)]
      congr 2
      ring

/--
---
conclusion: Lax342547.LeafTrimming.filtered_marginal
---
First compare the restricted mixed law pointwise to the original law,
then push this comparison through the projection. The original marginal
cap is charged only the actual mixed-law normalization cost.
-/
theorem filtered_marginal {Ω V : Type} [Fintype Ω] (p : PMF Ω) (μ : PMF V)
    (f : Ω → V) (S : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support)
    (M : ℝ≥0∞) (hp : ∀ v, p.map f v ≤ M * μ v) :
    ∀ v, (p.filter S hS).map f v ≤ (M / p.toOuterMeasure S) * μ v := by
  intro v
  have hd := Lax342547.Conditioning.filter_density p p S hS 1 (by simp)
  calc
    _ ≤ (1 / p.toOuterMeasure S) * p.map f v :=
      FiniteProbability.map_density (p.filter S hS) p _ hd f v
    _ ≤ (1 / p.toOuterMeasure S) * (M * μ v) :=
      mul_le_mul_of_nonneg_left (hp v) zero_le
    _ = _ := by simp only [div_eq_mul_inv, one_mul]; ac_rfl

/--
---
conclusion: Lax342547.LeafTrimming.combined_restriction
---
Successive normalizations cancel exactly, so several restrictions can
be charged to their combined intersection and retained mass.
-/
theorem combined_restriction {Ω : Type} [Fintype Ω] (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support)
    (hT : ∃ o ∈ T, o ∈ (p.filter S hS).support)
    (hST : ∃ o ∈ S ∩ T, o ∈ p.support) :
    (p.filter S hS).filter T hT = p.filter (S ∩ T) hST := by
  classical
  have hm0 := Conditioning.mass_ne_zero p S hS
  have hmtop := Conditioning.mass_ne_top p S
  ext o
  rw [PMF.filter_apply, ← PMF.toOuterMeasure_apply, Lax342547.Conditioning.filter_event,
    PMF.filter_apply, ← PMF.toOuterMeasure_apply]
  by_cases hs : o ∈ S
  · by_cases ht : o ∈ T
    · rw [Set.indicator_of_mem ht, PMF.filter_apply, ← PMF.toOuterMeasure_apply,
        Set.indicator_of_mem hs, Set.indicator_of_mem (show o ∈ S ∩ T from ⟨hs, ht⟩),
        ENNReal.inv_div (Or.inl hmtop) (Or.inl hm0)]
      simp only [div_eq_mul_inv]
      calc
        _ = p o * ((p.toOuterMeasure S)⁻¹ * p.toOuterMeasure S) *
            (p.toOuterMeasure (S ∩ T))⁻¹ := by ac_rfl
        _ = _ := by rw [ENNReal.inv_mul_cancel hm0 hmtop, mul_one]
    · simp [ht]
  · simp [hs, PMF.filter_apply]

end Lax342547Proofs.LeafTrimming
