import Lax342547.CollisionExponents
import Lax342547Proofs.RetainedImages

namespace Lax342547Proofs.CollisionExponents
open Lax342547.CollisionExponents

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.CollisionExponents.pruning_power_identity
---
-/
theorem pruning_power_identity (k Cn N : ℝ) :
    2 * (2 : ℝ)^(k*N) * (2 : ℝ)^Cn * (2 : ℝ)^(-(k+1/100)*N) =
      (2 : ℝ)^(1+Cn-N/100) := by
  have ht : (2 : ℝ) = (2 : ℝ)^(1 : ℝ) := by norm_num
  conv_lhs => arg 1; arg 1; arg 1; rw [ht]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/--
---
conclusion: Lax342547.CollisionExponents.pruning_overlap_bound
---
-/
theorem pruning_overlap_bound (keyCount cellCount k Cn N : ℝ)
    (_hkey0 : 0 ≤ keyCount) (hcell0 : 0 ≤ cellCount)
    (hkey : keyCount ≤ (2 : ℝ)^(k*N)) (hcell : cellCount ≤ (2 : ℝ)^Cn)
    (hscale : 1+Cn ≤ N/200) :
    2 * keyCount * cellCount * (2 : ℝ)^(-(k+1/100)*N) ≤ (2 : ℝ)^(-N/200) := by
  have hprod : 2 * keyCount * cellCount ≤ 2 * (2 : ℝ)^(k*N) * (2 : ℝ)^Cn :=
    mul_le_mul (mul_le_mul_of_nonneg_left hkey (by norm_num)) hcell hcell0
      (by positivity)
  calc
    _ ≤ (2 * (2 : ℝ)^(k*N) * (2 : ℝ)^Cn) * (2 : ℝ)^(-(k+1/100)*N) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = (2 : ℝ)^(1+Cn-N/100) := pruning_power_identity k Cn N
    _ ≤ (2 : ℝ)^(-N/200) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      linarith

/--
---
conclusion: Lax342547.CollisionExponents.scalar_agreement_power
---
-/
theorem scalar_agreement_power (s : ℕ) :
    1 / (2 : ℝ)^(s+1) = (2 : ℝ)^(-((s : ℝ)+1)) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [Nat.cast_add, Nat.cast_one, ← Real.rpow_natCast, one_div]

/--
---
conclusion: Lax342547.CollisionExponents.paper_scalar_smallness
---
-/
theorem paper_scalar_smallness (s : ℕ) (N : ℝ) (hs : (s : ℝ) ≤ N/100) (hN : 100 ≤ N) :
    (2 : ℝ)^(-(45/100 : ℝ)*N) ≤ 1/(2 : ℝ)^(s+1) := by
  rw [scalar_agreement_power]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  linarith

/--
---
conclusion: Lax342547.CollisionExponents.paper_scalar_cost
---
-/
theorem paper_scalar_cost (s : ℕ) (N : ℝ) (hs : (s : ℝ) ≤ N/100) (hN : 100 ≤ N) :
    (2 : ℝ)^(-N/50) ≤ 1/(2 : ℝ)^(s+1) := by
  rw [scalar_agreement_power]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  linarith

/--
---
conclusion: Lax342547.CollisionExponents.collision_lower_from_overlap
---
-/
theorem collision_lower_from_overlap (overlap retained error keys agreement holes : ℝ)
    (hkeys : 0 < keys) (hagreement : 0 ≤ agreement)
    (hpruning : overlap - keys * retained ≤ error)
    (hholes : agreement * retained ≤ holes) :
    agreement * (overlap-error) / keys ≤ holes := by
  have hret : (overlap-error)/keys ≤ retained := (div_le_iff₀ hkeys).mpr (by nlinarith)
  have h := (mul_le_mul_of_nonneg_left hret hagreement).trans hholes
  simpa only [mul_div_assoc] using h

end Lax342547Proofs.CollisionExponents
