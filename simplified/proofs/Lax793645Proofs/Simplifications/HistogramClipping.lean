import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteLaws
import Mathlib.Tactic

/-! Finite analytic ingredients for the proposed repeated-hit histogram route.
The many-query Fourier estimate and the sequential independence estimate remain
separate hypotheses; this file does not assert them from entropy bounds. -/
namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open scoped BigOperators
noncomputable section
variable {X : Type*} [Fintype X]

/-- The repeated-hit tail calculation. The pointwise lower bound represents
the sequential hit-and-independence estimate; the raw upper bound represents
the many-query Fourier estimate. Both are exposed hypotheses. -/
theorem repeated_hit_tail (μ π p H : Wgt X) (_hμ : IsLaw μ) (hπ : IsLaw π)
    (K B w C : ℝ) (hK : 0 ≤ K) (hB : 0 < B) (hw : 0 < w) (l : ℕ)
    (hcap : ∀ x, π x ≤ K*μ x) (hH : ∀ x, 0 ≤ H x)
    (hseq : ∀ x, B*w < p x → (B*w/2)^l ≤ H x)
    (hFourier : avg μ H ≤ C*w^l) :
    pr π (fun x => B*w < p x) ≤ K*C*(2/B)^l := by
  have hpos : 0 < (B*w/2)^l := pow_pos (by positivity) _
  have hlo : pr π (fun x => B*w < p x)*(B*w/2)^l ≤ avg π H := by
    rw [pr, ← avg_mul]
    apply avg_mono hπ.nz
    intro x
    by_cases h : B*w < p x
    · rw [ind_one h, one_mul]; exact hseq x h
    · rw [ind_zero h, zero_mul]; exact hH x
  have hu : avg π H ≤ K*avg μ H := by
    calc
      _ ≤ avg (fun x => K*μ x) H := avg_mono_left hH hcap
      _ = _ := by simp only [avg, ← mul_assoc, Finset.mul_sum]
  have hupper := hu.trans (mul_le_mul_of_nonneg_left hFourier hK)
  have he : (2/B)^l*(B*w/2)^l=w^l := by
    rw [← mul_pow]
    congr 1
    field_simp
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  calc
    _ ≤ K*(C*w^l) := hlo.trans hupper
    _ = (K*C*(2/B)^l)*(B*w/2)^l := by rw [mul_assoc (K*C), he]; ring

/-- Upper-tail control of a [0,1]-valued hit probability controls its mean. -/
theorem hit_mean_bound (π p : Wgt X) (hπ : IsLaw π)
    (hp1 : ∀ x, p x ≤ 1) (B w η : ℝ) (hBw : 0 ≤ B*w)
    (htail : pr π (fun x => B*w < p x) ≤ η) : avg π p ≤ B*w+η := by
  have hi (x : X) : p x ≤ B*w+ind (B*w < p x) := by
    by_cases h : B*w < p x
    · rw [ind_one h]; linarith [hp1 x]
    · rw [ind_zero h]; linarith
  have h := avg_mono hπ.nz hi
  rw [avg_add, hπ.avg_const] at h
  exact h.trans (add_le_add_right htail _)

/-- Uniform setwise domination is exactly what is needed for fixed-height
clipping; no lower bound on an individual cell's reference mass occurs here. -/
theorem clipping_from_setwise (d q : Wgt X) (B τ : ℝ)
    (hset : ∀ A : Finset X, (∑ x ∈ A, d x) ≤ B*(∑ x ∈ A, q x)+τ) :
    (∑ x, max (d x-B*q x) 0) ≤ τ := by
  classical
  let A := Finset.univ.filter fun x => 0 < d x-B*q x
  have he : (∑ x, max (d x-B*q x) 0) = ∑ x ∈ A, (d x-B*q x) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : 0 < d x-B*q x
    · simp [h, max_eq_left h.le]
    · simp [h, max_eq_right (le_of_not_gt h)]
  rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [hset A]

/-- Converse form, useful for tiny cells and every dominated filtered histogram. -/
theorem setwise_from_clipping (d q : Wgt X) (B τ : ℝ)
    (hclip : (∑ x, max (d x-B*q x) 0) ≤ τ) (A : Finset X) :
    (∑ x ∈ A, d x) ≤ B*(∑ x ∈ A, q x)+τ := by
  classical
  have h1 : (∑ x ∈ A, (d x - B*q x)) ≤ ∑ x ∈ A, max (d x-B*q x) 0 :=
    Finset.sum_le_sum fun x _ => le_max_left _ _
  have h2 : (∑ x ∈ A, max (d x-B*q x) 0) ≤ ∑ x, max (d x-B*q x) 0 :=
    Finset.sum_le_univ_sum_of_nonneg fun x => le_max_right _ _
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
  linarith

/-- Exact quadratic increment on the children of one parent cell. -/
theorem quadratic_refinement_identity (p w : Wgt X) (hw : ∀ x, w x ≠ 0)
    (P W : ℝ) (hW : W ≠ 0) (hp : ∑ x, p x = P) (hs : ∑ x, w x = W) :
    (∑ x, p x^2/w x)-P^2/W =
      ∑ x, (p x-P*w x/W)^2/w x := by
  have he (x : X) : (p x-P*w x/W)^2/w x =
      p x^2/w x - (2*P/W)*p x + (P^2/W^2)*w x := by
    field_simp [hw x, hW]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hp, hs]
  field_simp
  ring

/-- The deterministic bound on each good orientation, including all flags. -/
theorem flag_cell_energy_bound {V C : Type*} [Fintype V] [Fintype C]
    (a : V → C → ℝ) (r : V → ℝ) (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ v c, 0 ≤ a v c) (hr : ∀ v, 0 ≤ r v) (hw : ∀ c, 0 < w c)
    (htot : ∀ v, ∑ c, a v c = r v)
    (hcap : ∀ v c, a v c ≤ B*w c) :
    (∑ v, ∑ c, a v c^2/(r v*w c)) ≤ Fintype.card V * B := by
  have hv (v : V) : (∑ c, a v c^2/(r v*w c)) ≤ B := by
    by_cases hz : r v = 0
    · simp [hz, hB]
    · have hrp : 0 < r v := lt_of_le_of_ne (hr v) (Ne.symm hz)
      calc
        (∑ c, a v c^2/(r v*w c)) ≤ ∑ c, (B/r v)*a v c := by
          apply Finset.sum_le_sum
          intro c _
          apply (div_le_iff₀ (mul_pos hrp (hw c))).mpr
          have h := mul_le_mul_of_nonneg_left (hcap v c) (ha v c)
          field_simp
          nlinarith
        _ = B := by rw [← Finset.mul_sum, htot v]; exact div_mul_cancel₀ B hz
  calc
    _ ≤ ∑ _v : V, B := Finset.sum_le_sum fun v _ => hv v
    _ = _ := by simp

/-- Direct tiny-cell error estimate once clipping is available. -/
theorem omitted_split_cost {s c ds dc B τ δ : ℝ}
    (hs : 0 ≤ s) (hsc : s ≤ c) (hc : 0 < c) (hsδ : s ≤ δ)
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hds : ds ≤ B*s+τ) (hdc : dc ≤ B*c+τ) :
    2*(ds+(s/c)*dc) ≤ 4*B*δ+4*τ := by
  have hr : 0 ≤ s/c := div_nonneg hs hc.le
  have hr1 : s/c ≤ 1 := (div_le_one hc).mpr hsc
  have h := mul_le_mul_of_nonneg_left hdc hr
  have he : s/c*(B*c+τ) = B*s+(s/c)*τ := by field_simp
  rw [he] at h
  have ht := mul_le_mul_of_nonneg_right hr1 hτ
  have hb := mul_le_mul_of_nonneg_left hsδ hB
  nlinarith

end
end Lax793645Proofs.Simplifications
