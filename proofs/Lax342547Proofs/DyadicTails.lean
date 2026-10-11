import Lax342547.DyadicTails
import Lax342547Proofs.DyadicDeficits
import Mathlib.Algebra.BigOperators.Field

namespace Lax342547Proofs.DyadicTails
open Lax342547.DyadicTails

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/--
---
conclusion: Lax342547.DyadicTails.tail_deficit_nonneg
---
-/
theorem tail_deficit_nonneg (a : ℕ → ℝ) (ha : Antitone a) (s b : ℕ) (hb : 0 < b) :
    0 ≤ tailDeficit a s b := by
  have hh : tailSum a s b ≤ (b : ℝ)*a (s-b) := by
    calc
      _ ≤ ∑ t ∈ Finset.range b, a (s-b) := Finset.sum_le_sum (fun t ht => ha (by omega))
      _ = _ := by simp [mul_comm]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  unfold tailDeficit
  exact sub_nonneg.mpr ((div_le_iff₀ hb').mpr (by simpa [mul_comm] using hh))

/--
---
conclusion: Lax342547.DyadicTails.tail_deficit_le
---
-/
theorem tail_deficit_le (a : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) (s b : ℕ) :
    tailDeficit a s b ≤ a (s-b) := by
  have hh : 0 ≤ tailSum a s b := Finset.sum_nonneg (fun t _ => ha _)
  unfold tailDeficit
  exact sub_le_self _ (div_nonneg hh (Nat.cast_nonneg _))

/--
---
conclusion: Lax342547.DyadicTails.dyadic_recurrence
---
-/
theorem dyadic_recurrence (a : ℕ → ℝ) (ha : Antitone a) (s b : ℕ)
    (hb : 0 < b) (hbs : 2*b ≤ s) :
    2*tailDeficit a s (2*b) ≤ 2*(a (s-2*b)-a (s-b))+tailDeficit a s b := by
  have hindex : s-2*b+b = s-b := by omega
  have hsum : tailSum a s (2*b) = (∑ t ∈ Finset.range b, a (s-2*b+t))+tailSum a s b := by
    unfold tailSum
    rw [show 2*b=b+b by omega,Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    omega
  have hfirst : (b : ℝ)*a (s-b) ≤ ∑ t ∈ Finset.range b, a (s-2*b+t) := by
    calc
      _ = ∑ t ∈ Finset.range b, a (s-b) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun t ht => ha (by have := Finset.mem_range.mp ht; omega))
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  unfold tailDeficit
  rw [hsum]
  push_cast
  field_simp
  nlinarith

end Lax342547Proofs.DyadicTails
