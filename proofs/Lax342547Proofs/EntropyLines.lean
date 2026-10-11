import Lax342547.EntropyLines
import Lax342547Proofs.RelativeEntropy
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace Lax342547Proofs.EntropyLines
open Lax342547.EntropyLines

set_option backward.isDefEq.respectTransparency false
open Lax342547.RelativeEntropy
open scoped Topology BigOperators
open Filter

/--
---
conclusion: Lax342547.EntropyLines.mix_derivative
---
-/
theorem mix_derivative {Ω : Type} (ρ ρ' : Ω → ℝ) (x : Ω) :
    HasDerivAt (fun t => mix ρ ρ' t x) (ρ' x-ρ x) 0 := by
  convert (((hasDerivAt_id (0:ℝ)).const_sub 1).mul_const (ρ x)).add
    ((hasDerivAt_id (0:ℝ)).mul_const (ρ' x)) using 1 <;> first | rfl | ring

/--
---
conclusion: Lax342547.EntropyLines.old_entropy_derivative
---
-/
theorem old_entropy_derivative {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ) :
    HasDerivAt (oldEntropy ρ ρ' q) (oldDerivative ρ ρ' q) 0 := by
  classical
  unfold oldEntropy oldDerivative
  apply HasDerivAt.fun_sum
  intro x _
  by_cases hx : ρ x = 0
  · simp only [hx, if_true]
    exact hasDerivAt_const 0 0
  · simp only [hx, if_false]
    have hl := mix_derivative ρ ρ' x
    have he : mix ρ ρ' 0 x = ρ x := by simp [mix]
    have hm := (Real.hasDerivAt_mul_log (by rw [he]; exact hx)).comp 0 hl
    have hd := hm.sub (hl.mul_const (Real.log (q x)))
    convert hd using 1
    · rfl
    · rw [he]; ring

/--
---
conclusion: Lax342547.EntropyLines.entropy_mix_identity
---
-/
theorem entropy_mix_identity {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ)
    (hρ' : ∀ x, 0 ≤ ρ' x) (t : ℝ) (ht : 0 < t) :
    entropy (mix ρ ρ' t) q = oldEntropy ρ ρ' q t + t*newMass ρ ρ'*Real.log t + t*newEntropy ρ ρ' q := by
  classical
  unfold entropy oldEntropy newMass newEntropy
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ρ x = 0
  · simp only [hx, if_true, mix, mul_zero, zero_add]
    by_cases hx' : ρ' x = 0
    · simp [hx', coordinate]
    · have hp : 0 < ρ' x := lt_of_le_of_ne (hρ' x) (Ne.symm hx')
      rw [Real.log_mul ht.ne' hp.ne']
      unfold coordinate
      ring
  · simp [hx, coordinate]

/--
---
conclusion: Lax342547.EntropyLines.old_entropy_zero
---
-/
theorem old_entropy_zero {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ) :
    oldEntropy ρ ρ' q 0 = entropy ρ q := by
  classical
  unfold oldEntropy entropy
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ρ x = 0 <;> simp [hx, coordinate, mix]

/--
---
conclusion: Lax342547.EntropyLines.entropy_new_support_slope
---
-/
theorem entropy_new_support_slope {Ω : Type} [Fintype Ω] (ρ ρ' q : Ω → ℝ)
    (hρ' : ∀ x, 0 ≤ ρ' x) (hnew : 0 < newMass ρ ρ') :
    Tendsto (fun t => (entropy (mix ρ ρ' t) q-entropy ρ q)/t) (𝓝[>] 0) atBot := by
  have hold := (old_entropy_derivative ρ ρ' q).tendsto_slope_zero_right
  have hold' : Tendsto (fun t => (oldEntropy ρ ρ' q t-oldEntropy ρ ρ' q 0)/t)
      (𝓝[>] 0) (𝓝 (oldDerivative ρ ρ' q)) := by
    simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using hold
  have hlog := Real.tendsto_log_nhdsGT_zero.const_mul_atBot hnew
  have h := hlog.atBot_add (hold'.add_const (newEntropy ρ ρ' q))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Set.mem_Ioi] at ht
  rw [entropy_mix_identity ρ ρ' q hρ' t ht, old_entropy_zero]
  field_simp
  ring

end Lax342547Proofs.EntropyLines
