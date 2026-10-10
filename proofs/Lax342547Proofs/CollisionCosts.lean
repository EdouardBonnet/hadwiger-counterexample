import Lax342547.CollisionCosts
import Lax342547Proofs.CollisionExponents
import Lax342547Proofs.PairRecovery

namespace Lax342547Proofs.CollisionCosts
open Lax342547.CollisionCosts

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.CollisionCosts.pruning_half_overlap
---
-/
theorem pruning_half_overlap (η N overlap : ℝ)
    (hscale : 1 ≤ (1/200-η)*N) (hoverlap : (2:ℝ)^(-η*N) ≤ overlap) :
    (2:ℝ)^(-N/200) ≤ overlap/2 := by
  have he : (2:ℝ)^(-η*N-1) = (2:ℝ)^(-η*N)/2 := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    norm_num
  calc
    (2:ℝ)^(-N/200) ≤ (2:ℝ)^(-η*N-1) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      nlinarith
    _ = (2:ℝ)^(-η*N)/2 := he
    _ ≤ overlap/2 := by linarith

/--
---
conclusion: Lax342547.CollisionCosts.collision_exponential_lower
---
-/
theorem collision_exponential_lower (k η N keys overlap error agreement holes : ℝ)
    (hkeys : 0 < keys) (hkeybound : keys ≤ (2:ℝ)^(k*N))
    (hoverlap : (2:ℝ)^(-η*N) ≤ overlap)
    (herror : error ≤ (2:ℝ)^(-N/200)) (hscale : 1 ≤ (1/200-η)*N)
    (hagreement : (2:ℝ)^(-N/50) ≤ agreement)
    (hholes : agreement*(overlap-error)/keys ≤ holes) :
    (2:ℝ)^(-((k+1/50+η)*N)-1) ≤ holes := by
  have ht : (2:ℝ)^(-η*N)/2 ≤ overlap-error := by
    have hp := pruning_half_overlap η N ((2:ℝ)^(-η*N)) hscale le_rfl
    linarith
  have hg : 0 ≤ overlap-error := le_trans (by positivity) ht
  have hp : (2:ℝ)^(-N/50)*((2:ℝ)^(-η*N)/2) ≤ agreement*(overlap-error) :=
    mul_le_mul hagreement ht (by positivity) (le_trans (by positivity) hagreement)
  calc
    (2:ℝ)^(-((k+1/50+η)*N)-1) =
        ((2:ℝ)^(-N/50)*((2:ℝ)^(-η*N)/2))/(2:ℝ)^(k*N) := by
      rw [show -((k+1/50+η)*N)-1 = (-N/50+(-η*N))-(k*N)-1 by ring]
      rw [Real.rpow_sub (by norm_num : (0:ℝ)<2), Real.rpow_sub (by norm_num : (0:ℝ)<2),
        Real.rpow_add (by norm_num : (0:ℝ)<2)]
      norm_num
      ring
    _ ≤ (agreement*(overlap-error))/keys := by
      have hd : ((2:ℝ)^(-N/50)*((2:ℝ)^(-η*N)/2))/(2:ℝ)^(k*N) ≤
          ((2:ℝ)^(-N/50)*((2:ℝ)^(-η*N)/2))/keys := by
        exact div_le_div_of_nonneg_left (by positivity) hkeys hkeybound
      exact hd.trans (div_le_div_of_nonneg_right hp hkeys.le)
    _ ≤ holes := hholes

/--
---
conclusion: Lax342547.CollisionCosts.restriction_exponential_lower
---
-/
theorem restriction_exponential_lower (k η N mass restricted original : ℝ)
    (hmass : (2:ℝ)^(-η*N) ≤ mass)
    (hrestricted : (2:ℝ)^(-((k+1/50+η)*N)-1) ≤ restricted)
    (hrecovery : mass^2*restricted ≤ original) :
    (2:ℝ)^(-((k+1/50+3*η)*N)-1) ≤ original := by
  have hm0 : 0 ≤ mass := le_trans (by positivity) hmass
  have hp : ((2:ℝ)^(-η*N))^2 ≤ mass^2 := pow_le_pow_left₀ (by positivity) hmass 2
  calc
    (2:ℝ)^(-((k+1/50+3*η)*N)-1) =
        ((2:ℝ)^(-η*N))^2*(2:ℝ)^(-((k+1/50+η)*N)-1) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      norm_num
      ring
    _ ≤ mass^2*restricted := mul_le_mul hp hrestricted (by positivity) (sq_nonneg mass)
    _ ≤ original := hrecovery

end Lax342547Proofs.CollisionCosts
