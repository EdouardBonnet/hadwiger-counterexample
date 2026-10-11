import Lax342547.SplitTrimming
import Lax342547.LeafTrimming
import Lax342547.MetadataPins

namespace Lax342547Proofs.SplitTrimming

open Lax342547.MomentSpace Lax342547.MetadataPins
open scoped ENNReal

/--
---
conclusion: Lax342547.SplitTrimming.small_fibers
---
The discarded points are covered by small fibers, each of mass below the
threshold. A finite union bound pays the number of possible split records.
-/
theorem small_fibers {Ω K : Type} [Fintype K] (p : PMF Ω) (f : Ω → K) (τ : ℝ≥0∞) :
    p.toOuterMeasure {o | p.toOuterMeasure {x | f x = f o} < τ} ≤ Fintype.card K * τ := by
  classical
  let S (k : K) : Set Ω := {o | f o = k ∧ p.toOuterMeasure {x | f x = k} < τ}
  have hcover : {o | p.toOuterMeasure {x | f x = f o} < τ} ⊆ ⋃ k, S k :=
    fun o ho => Set.mem_iUnion.mpr ⟨f o, rfl, ho⟩
  have hb (k : K) : p.toOuterMeasure (S k) ≤ τ := by
    by_cases h : p.toOuterMeasure {x | f x = k} < τ
    · exact (p.toOuterMeasure.mono (fun _ hx => hx.1)).trans h.le
    · have he : S k = ∅ := by ext o; simp [S, h]
      simp [he]
  calc
    _ ≤ p.toOuterMeasure (⋃ k, S k) := p.toOuterMeasure.mono hcover
    _ ≤ ∑ k, p.toOuterMeasure (S k) := MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : K, τ := Finset.sum_le_sum (fun k _ => hb k)
    _ = _ := by simp

/--
---
conclusion: Lax342547.SplitTrimming.metadata_discard
---
The record count is at most 2^(a n + u N). Multiplying by the cutoff
2^(-(u+1)N) leaves the exact metadata cost 2^(a n - N).
-/
theorem metadata_discard {Ω J Axis I N : Type}
    [Fintype J] [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (choice : Ω → J) (S : J → Axis → Submodule Binary (I → Binary)) (a n u : ℕ)
    (hchoices : Fintype.card J ≤ 2 ^ (a * n))
    (hu : ∀ j, ∑ b, Module.finrank Binary (S j b) ≤ u) :
    p.toOuterMeasure {o | p.toOuterMeasure {x | record A choice S x = record A choice S o} <
        (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N))} ≤
      (2 : ℝ≥0∞) ^ ((a * n : ℕ) - (Fintype.card N : ℝ)) := by
  have hc : Fintype.card (Key N S) ≤ 2 ^ (a * n + u * Fintype.card N) := by
    rw [← Nat.card_eq_fintype_card, pow_add]
    exact (Lax342547.MetadataPins.key_count S u hu).trans (Nat.mul_le_mul_right _ hchoices)
  have hc' : (Fintype.card (Key N S) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (a * n + u * Fintype.card N) := by
    exact_mod_cast hc
  calc
    _ ≤ Fintype.card (Key N S) * (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N)) :=
      Lax342547.SplitTrimming.small_fibers p (record A choice S) _
    _ ≤ (2 : ℝ≥0∞) ^ (a * n + u * Fintype.card N) *
        (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N)) :=
      mul_le_mul_of_nonneg_right hc' zero_le
    _ = _ := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      congr 1
      push_cast
      ring

/--
---
conclusion: Lax342547.SplitTrimming.exponential_discard
---
A single ambient scale paying twice the metadata coefficient leaves a
uniform exponentially small discarded fraction, independent of the law.
-/
theorem exponential_discard {Ω J Axis I N : Type}
    [Fintype J] [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (choice : Ω → J) (S : J → Axis → Submodule Binary (I → Binary)) (a n u : ℕ)
    (hchoices : Fintype.card J ≤ 2 ^ (a * n))
    (hu : ∀ j, ∑ b, Module.finrank Binary (S j b) ≤ u)
    (hscale : 2 * a * n ≤ Fintype.card N) :
    p.toOuterMeasure {o | p.toOuterMeasure {x | record A choice S x = record A choice S o} <
        (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N))} ≤
      (2 : ℝ≥0∞) ^ (-(Fintype.card N : ℝ) / 2) := by
  apply (Lax342547.SplitTrimming.metadata_discard p A choice S a n u hchoices hu).trans
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hscale' : 2 * (a : ℝ) * n ≤ Fintype.card N := by exact_mod_cast hscale
  push_cast
  linarith

/--
---
conclusion: Lax342547.SplitTrimming.repinning_density
---
Charge the preceding retained leaf fraction and the retained metadata
fiber separately. Their two exact normalization costs fit inside D'.
-/
theorem repinning_density {Ω : Type} (p μ : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support)
    (hT : ∃ o ∈ T, o ∈ (p.filter S hS).support)
    (D ζ : ℝ) (N K₁ u : ℕ) (hζ : ζ ≤ 1)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * N)) ≤ p.toOuterMeasure S)
    (hTbound : (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * N)) ≤ (p.filter S hS).toOuterMeasure T)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ ((D + K₁ + 1) * N) * μ o) :
    ∀ o, ((p.filter S hS).filter T hT) o ≤
      (2 : ℝ≥0∞) ^ ((D + K₁ + u + 5) * N) * μ o := by
  have hfirst := Lax342547.LeafTrimming.density_after_restriction p μ S hS (D + K₁ + 1) ζ N hSbound hp
  have hsecond := Lax342547.LeafTrimming.density_after_restriction (p.filter S hS) μ T hT
    (D + K₁ + 1 + ζ) ((u : ℝ) + 1) N hTbound hfirst
  intro o
  apply (hsecond o).trans
  apply mul_le_mul_of_nonneg_right _ zero_le
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hn : (0 : ℝ) ≤ N := by positivity
  exact mul_le_mul_of_nonneg_right (by linarith) hn

end Lax342547Proofs.SplitTrimming
