import Lax342547.RestrictedLeaves
import Lax342547Proofs.Conditioning
import Lax342547.Conditioning
import Lax342547.LeafTrimming

namespace Lax342547Proofs.RestrictedLeaves

open Lax342547.MomentSpace Lax342547.ExactPins
open Lax342547.LeafTrimming Lax342547.BoundedPeeling
open scoped ENNReal

theorem rank_power (ζ : ℝ) (n t : ℕ) :
    ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n))) ^ t = (2 : ℝ≥0∞) ^ (-((1 - ζ) * t * n)) := by
  rw [← ENNReal.rpow_mul_natCast]
  congr 1
  ring

/--
---
conclusion: Lax342547.RestrictedLeaves.restricted_family
---
Use the combined retained mass to bound discarded weight. Every retained
leaf has a positive restriction mass, and its normalization preserves all
quotient-rank image tests with the stated loss. Retain exact weighted
recovery and the explicit absolute joint density factor.
-/
theorem restricted_family {Ω J Axis I N : Type}
    [Fintype Ω] [Fintype J] [Fintype Axis]
    (p : J → PMF Ω) (μ : PMF Ω)
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : J → Pin Axis I N) (S : J → Set Ω) (w : J → ℝ≥0∞)
    (C ζ η : ℝ) (n : ℕ) (hζ : 0 ≤ ζ) (hw : ∑ j, w j ≤ 1)
    (hq : (2 : ℝ≥0∞) ^ (-(η * n)) ≤ ∑ j, w j * (p j).toOuterMeasure (S j))
    (hcap : ∀ j (Q : Pin Axis I N), 1 ≤ (P j).relativeRank Q →
      (p j).toOuterMeasure (Q.event A) ≤
        ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n))) ^ (P j).relativeRank Q)
    (hdensity : ∀ j o, p j o ≤ (2 : ℝ≥0∞) ^ (C * n) * μ o) :
    discardedMass w (fun j => (p j).toOuterMeasure (S j)) ((2 : ℝ≥0∞) ^ (-(ζ * n))) /
        (∑ j, w j * (p j).toOuterMeasure (S j)) ≤ (2 : ℝ≥0∞) ^ (-((ζ - η) * n)) ∧
    ∀ j, (2 : ℝ≥0∞) ^ (-(ζ * n)) ≤ (p j).toOuterMeasure (S j) →
      LawBound (p j) μ A (P j) (S j)
        ((2 : ℝ≥0∞) ^ (-((1 - 2 * ζ) * n))) ((2 : ℝ≥0∞) ^ ((C + ζ) * n)) := by
  refine ⟨Lax342547.LeafTrimming.restricted_discard w _ ζ η n hw hq, ?_⟩
  intro j hj
  have hpos : 0 < (p j).toOuterMeasure (S j) :=
    (ENNReal.rpow_pos (by norm_num) (by norm_num)).trans_le hj
  have hS := Conditioning.support_of_positive (p j) (S j) hpos
  refine ⟨hS, ?_, ?_, Lax342547.Conditioning.weighted_filter (p j) (S j) hS⟩
  · intro Q hQ
    rw [rank_power]
    exact Lax342547.LeafTrimming.minentropy_after_restriction (p j) (S j) (Q.event A) hS ζ n
      ((P j).relativeRank Q) hζ hQ hj (by simpa only [rank_power] using hcap j Q hQ)
  · exact Lax342547.LeafTrimming.density_after_restriction (p j) μ (S j) hS C ζ n hj (hdensity j)

/--
---
conclusion: Lax342547.RestrictedLeaves.weighted_residual
---
The residual budget for a fresh peeling is relative to its part. Summing
with the actual part weights gives the same budget for the whole mixture.
-/
theorem weighted_residual {J : Type} [Fintype J] (w r : J → ℝ≥0∞) (δ : ℝ≥0∞)
    (hw : ∑ j, w j ≤ 1) (hr : ∀ j, r j ≤ δ) : ∑ j, w j * r j ≤ δ := by
  calc
    _ ≤ ∑ j, w j * δ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hr j) zero_le)
    _ = (∑ j, w j) * δ := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hw zero_le
    _ = δ := one_mul _

end Lax342547Proofs.RestrictedLeaves
