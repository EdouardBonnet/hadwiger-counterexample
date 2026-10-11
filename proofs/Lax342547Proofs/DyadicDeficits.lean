import Lax342547.DyadicDeficits
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Lax342547Proofs.DyadicDeficits
open Lax342547.DyadicDeficits

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/--
---
conclusion: Lax342547.DyadicDeficits.sum_shift
---
-/
theorem sum_shift (v : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, v (j+1)) = (∑ j ∈ Finset.range n, v j)-v 0+v n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    rw [ih]
    ring

/--
---
conclusion: Lax342547.DyadicDeficits.sum_differences
---
-/
theorem sum_differences (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (f j-f (j+1))) = f 0-f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    ring

/--
---
conclusion: Lax342547.DyadicDeficits.deficit_ratio_sum
---
-/
theorem deficit_ratio_sum (f v : ℕ → ℝ) (n : ℕ) (r : ℝ)
    (hrec : ∀ j < n, 2*v j ≤ 2*(f j-f (j+1))+v (j+1))
    (hf0 : f 0 ≤ r) (hfn : 0 ≤ f n) (hv0 : 0 ≤ v 0) (hvn : v n ≤ f n) :
    (∑ j ∈ Finset.range n, v j) ≤ 2*r := by
  have hh := Finset.sum_le_sum (s := Finset.range n) (fun j hj => hrec j (Finset.mem_range.mp hj))
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,sum_differences,sum_shift] at hh
  linarith

/--
---
conclusion: Lax342547.DyadicDeficits.two_mode_scale
---
-/
theorem two_mode_scale (fC fR vC vR : ℕ → ℝ) (n : ℕ) (r : ℝ)
    (hC : ∀ j < n, 2*vC j ≤ 2*(fC j-fC (j+1))+vC (j+1))
    (hR : ∀ j < n, 2*vR j ≤ 2*(fR j-fR (j+1))+vR (j+1))
    (hfC0 : fC 0 ≤ r) (hfR0 : fR 0 ≤ r)
    (hfCn : 0 ≤ fC n) (hfRn : 0 ≤ fR n)
    (hvC0 : 0 ≤ vC 0) (hvR0 : 0 ≤ vR 0)
    (hvCn : vC n ≤ fC n) (hvRn : vR n ≤ fR n) (hn : 16*r < n) :
    ∃ j < n, vC j+vR j < 1/4 := by
  have hc := deficit_ratio_sum fC vC n r hC hfC0 hfCn hvC0 hvCn
  have hr := deficit_ratio_sum fR vR n r hR hfR0 hfRn hvR0 hvRn
  by_contra hh
  push Not at hh
  have hsum : (n : ℝ)*(1/4) ≤ ∑ j ∈ Finset.range n, (vC j+vR j) := by
    calc
      _ = ∑ j ∈ Finset.range n, (1/4 : ℝ) := by simp [nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hh j (Finset.mem_range.mp hj))
  rw [Finset.sum_add_distrib] at hsum
  linarith

end Lax342547Proofs.DyadicDeficits
