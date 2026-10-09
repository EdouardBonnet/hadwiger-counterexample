import Lax342547.BoundedPeeling
import Lax342547Proofs.LeafPartition
import Lax342547Proofs.PeelingBudget
import Lax342547Proofs.Conditioning
import Lax342547Proofs.FiniteProbability

namespace Lax342547Proofs.BoundedPeeling

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.LeafPartition
open Lax342547.BoundedPeeling
open scoped ENNReal

theorem event_upper {Ω Axis I N : Type}
    [Fintype Ω] [Fintype Axis] [Fintype I]
    (p μ : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (D ε : ℝ) (n : ℕ) (hε : ε ≤ 1)
    (hdensity : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ (D * n) * μ o)
    (hreference : ∀ P : Pin Axis I N,
      μ.toOuterMeasure (P.event A) ≤ (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * n)))
    (P : Pin Axis I N) (S : Set Ω) (hS : S ⊆ P.event A) (u : ℕ) (hu : u ≤ P.rank) :
    p.toOuterMeasure S ≤ (2 : ℝ≥0∞) ^ (D * n) * ((2 : ℝ≥0∞) ^ (-((1 - ε) * n))) ^ u := by
  have hμ := (μ.toOuterMeasure.mono hS).trans (hreference P)
  have hu' : (u : ℝ) ≤ P.rank := by exact_mod_cast hu
  have hn : (0 : ℝ) ≤ n := by positivity
  have hcoeff : 0 ≤ 1 - ε := by linarith
  have hexp : -((1 - ε) * P.rank * n) ≤ -((1 - ε) * n) * u := by
    have h := mul_le_mul_of_nonneg_left hu' (mul_nonneg hcoeff hn)
    nlinarith
  calc
    _ ≤ (2 : ℝ≥0∞) ^ (D * n) * μ.toOuterMeasure S := FiniteProbability.event_density p μ _ hdensity S
    _ ≤ (2 : ℝ≥0∞) ^ (D * n) * (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * n)) :=
      mul_le_mul_of_nonneg_left hμ zero_le
    _ ≤ _ := by
      rw [← ENNReal.rpow_mul_natCast]
      exact mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp) zero_le

/--
---
conclusion: Lax342547.BoundedPeeling.bounded_partition
---
Extract the disjoint partition while retaining the original masses.
The absolute reference cap and density bound control each cumulative
new rank. Normalize only at the end, keeping the exact conditional
event bounds, uniform density cost, and pointwise mass recovery.
-/
theorem bounded_partition {Ω Axis I N : Type}
    [Fintype Ω] [DecidableEq Ω] [Fintype Axis] [Fintype I] [Fintype N]
    (p μ : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Finset Ω) (hR : (R : Set Ω) ⊆ P₀.event A)
    (D ζ ε : ℝ) (n K : ℕ) (hn : 0 < n)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : ε ≤ ζ / 4) (hK : 4 * (D + 1) / ζ ≤ K)
    (hdensity : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ (D * n) * μ o)
    (hreference : ∀ P : Pin Axis I N,
      μ.toOuterMeasure (P.event A) ≤ (2 : ℝ≥0∞) ^ (-((1 - ε) * P.rank * n))) :
    ∃ L : Finset (Finset Ω × Pin Axis I N),
      Partition p A P₀ R ((2 : ℝ≥0∞) ^ (-(ζ * n))) ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n))) L ∧
      ∀ z ∈ L, z.2.rank - P₀.rank ≤ K ∧
        LawBound p μ A z.2 z.1 ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n)))
          ((2 : ℝ≥0∞) ^ ((D + K + 1) * n)) := by
  obtain ⟨L, hL⟩ := LeafPartition.exists_partition p A P₀ R hR
    ((2 : ℝ≥0∞) ^ (-(ζ * n))) ((2 : ℝ≥0∞) ^ (-((1 - ζ) * n)))
    (ne_of_gt (ENNReal.rpow_pos (by norm_num) (by norm_num)))
    (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))
  refine ⟨L, hL, fun z hz => ?_⟩
  obtain ⟨_, _, hpin, hmass, hgood⟩ := hL.1 z hz
  have hupper := event_upper p μ A D ε n (by linarith) hdensity hreference z.2 z.1 hpin
    (z.2.rank - P₀.rank) (Nat.sub_le _ _)
  have hcompare := PeelingBudget.rank_comparison D ζ ε n (z.2.rank - P₀.rank) hn _ hmass hupper
  have hrank := PeelingBudget.conservative_rank_bound D ζ ε (z.2.rank - P₀.rank) hζ hζ₁ hε hcompare
  have hu : z.2.rank - P₀.rank ≤ K := by exact_mod_cast (le_of_lt (hrank.trans_le hK))
  have hs : ∃ o ∈ (z.1 : Set Ω), o ∈ p.support :=
    Conditioning.support_of_positive p z.1 (lt_of_le_of_lt zero_le hmass)
  have hcost := PeelingBudget.density_cost D ζ n (z.2.rank - P₀.rank) K hζ.le hζ₁ hu _ hmass.le
  refine ⟨hu, hs, ?_, ?_, ?_⟩
  · intro Q hQ
    exact Conditioning.filter_event_bound p z.1 (Q.event A) hs _ (hgood Q hQ)
  · intro o
    exact (Conditioning.filter_density p μ z.1 hs _ hdensity o).trans
      (mul_le_mul_of_nonneg_right hcost zero_le)
  · exact Conditioning.weighted_filter p z.1 hs

end Lax342547Proofs.BoundedPeeling
