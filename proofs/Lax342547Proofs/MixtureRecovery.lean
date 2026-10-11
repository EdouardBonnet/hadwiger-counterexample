import Lax342547.MixtureRecovery
import Lax342547Proofs.Conditioning
import Lax342547.Conditioning

namespace Lax342547Proofs.MixtureRecovery

open scoped ENNReal

/--
---
conclusion: Lax342547.MixtureRecovery.mixture_event
---
Sum the pointwise mixture identity over the event and interchange the two
finite sums. Each conditional leaf keeps its actual original weight.
-/
theorem mixture_event {Ω J : Type} [Fintype Ω] [Fintype J]
    (p : J → PMF Ω) (q : PMF Ω) (w : J → ℝ≥0∞)
    (hq : ∀ o, q o = ∑ j, w j * p j o) (S : Set Ω) :
    q.toOuterMeasure S = ∑ j, w j * (p j).toOuterMeasure S := by
  classical
  simp only [PMF.toOuterMeasure_apply_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : o ∈ S
  · simp only [Set.indicator_of_mem ho, hq]
  · simp [ho]

/--
---
conclusion: Lax342547.MixtureRecovery.nested_weighted_filter
---
Cancel the inner conditional normalization first and then the outer one.
Their actual masses recover precisely the combined restricted point mass.
-/
theorem nested_weighted_filter {Ω : Type} (p : PMF Ω) (S T : Set Ω)
    (hS : ∃ o ∈ S, o ∈ p.support)
    (hT : ∃ o ∈ T, o ∈ (p.filter S hS).support) (o : Ω) :
    p.toOuterMeasure S * (p.filter S hS).toOuterMeasure T * ((p.filter S hS).filter T hT) o =
      (S ∩ T).indicator p o := by
  classical
  rw [mul_assoc, Lax342547.Conditioning.weighted_filter]
  by_cases ht : o ∈ T
  · rw [Set.indicator_of_mem ht, Lax342547.Conditioning.weighted_filter]
    by_cases hs : o ∈ S <;> simp [hs, ht]
  · simp [ht]

/--
---
conclusion: Lax342547.MixtureRecovery.conditional_event_mass
---
A conditional residual cap translates back to original mass by multiplying
by that part's positive finite mass. No uniform reweighting is involved.
-/
theorem conditional_event_mass {Ω : Type} [Fintype Ω] (p : PMF Ω)
    (S T : Set Ω) (hS : ∃ o ∈ S, o ∈ p.support) (hT : T ⊆ S)
    (δ : ℝ≥0∞) (hb : (p.filter S hS).toOuterMeasure T ≤ δ) :
    p.toOuterMeasure T ≤ δ * p.toOuterMeasure S := by
  rw [Lax342547.Conditioning.filter_event, Set.inter_eq_right.mpr hT] at hb
  exact (ENNReal.div_le_iff (Conditioning.mass_ne_zero p S hS) (Conditioning.mass_ne_top p S)).mp hb

theorem fiber_mass_sum {Ω K : Type} [Fintype K] (p : PMF Ω) (f : Ω → K) :
    ∑ k, p.toOuterMeasure {o | f o = k} = 1 := by
  have he (k : K) : p.toOuterMeasure {o | f o = k} = p.map f k := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl
  simp_rw [he]
  simpa only [tsum_fintype] using (p.map f).tsum_coe

/--
---
conclusion: Lax342547.MixtureRecovery.fiber_residual
---
Cover the retained-fiber residuals by their individual parts, multiply
their relative budgets by the original fiber masses, and sum to delta.
The discarded small fibers are charged separately at their actual mass.
-/
theorem fiber_residual {Ω K : Type} [Fintype K] (p : PMF Ω) (f : Ω → K)
    (R : K → Set Ω) (τ δ : ℝ≥0∞)
    (hr : ∀ k, τ ≤ p.toOuterMeasure {o | f o = k} →
      p.toOuterMeasure (R k) ≤ δ * p.toOuterMeasure {o | f o = k}) :
    p.toOuterMeasure ({o | p.toOuterMeasure {x | f x = f o} < τ} ∪
        {o | τ ≤ p.toOuterMeasure {x | f x = f o} ∧ o ∈ R (f o)}) ≤
      p.toOuterMeasure {o | p.toOuterMeasure {x | f x = f o} < τ} + δ := by
  classical
  let T (k : K) : Set Ω := {o | τ ≤ p.toOuterMeasure {x | f x = k} ∧ o ∈ R k}
  have hcover : {o | τ ≤ p.toOuterMeasure {x | f x = f o} ∧ o ∈ R (f o)} ⊆ ⋃ k, T k :=
    fun o ho => Set.mem_iUnion.mpr ⟨f o, ho⟩
  have hb (k : K) : p.toOuterMeasure (T k) ≤ δ * p.toOuterMeasure {o | f o = k} := by
    by_cases hk : τ ≤ p.toOuterMeasure {o | f o = k}
    · exact (p.toOuterMeasure.mono (fun _ hx => hx.2)).trans (hr k hk)
    · have he : T k = ∅ := by ext o; simp [T, hk]
      simp [he]
  have hres : p.toOuterMeasure {o | τ ≤ p.toOuterMeasure {x | f x = f o} ∧ o ∈ R (f o)} ≤ δ := by
    calc
      _ ≤ p.toOuterMeasure (⋃ k, T k) := p.toOuterMeasure.mono hcover
      _ ≤ ∑ k, p.toOuterMeasure (T k) := MeasureTheory.measure_iUnion_fintype_le _ _
      _ ≤ ∑ k, δ * p.toOuterMeasure {o | f o = k} := Finset.sum_le_sum (fun k _ => hb k)
      _ = δ := by rw [← Finset.mul_sum, fiber_mass_sum, mul_one]
  exact (MeasureTheory.measure_union_le _ _).trans (add_le_add le_rfl hres)

end Lax342547Proofs.MixtureRecovery
