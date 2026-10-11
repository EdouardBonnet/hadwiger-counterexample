import Lax342547.ModeBudgets
import Lax342547Proofs.ListDeficits

namespace Lax342547Proofs.ModeBudgets
open Lax342547.ModeBudgets

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/--
---
conclusion: Lax342547.ModeBudgets.mode_span_budget
---
-/
theorem mode_span_budget {K V ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : ι → Submodule K V) (r : ℝ) (hr : 0 ≤ r)
    (hS : ∀ i, (Module.finrank K (S i) : ℝ) ≤ r) (I : Finset ι) :
    (Module.finrank K (I.sup S : Submodule K V) : ℝ) ≤ r*Fintype.card ι := by
  have hh := Lax342547Proofs.SumEnvelope.span_dimension_sum_bound (fun i : I => S i.val)
  rw [Lax342547Proofs.ListDeficits.finset_span_eq,Finset.sum_coe_sort I (fun i => Module.finrank K (S i))] at hh
  have hh' : (Module.finrank K (I.sup S : Submodule K V) : ℝ) ≤ ∑ i ∈ I, (Module.finrank K (S i) : ℝ) := by exact_mod_cast hh
  calc
    _ ≤ _ := hh'
    _ ≤ ∑ i ∈ I, r := Finset.sum_le_sum (fun i _ => hS i)
    _ = r*(I.card : ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.card_le_univ I)) hr

end Lax342547Proofs.ModeBudgets
