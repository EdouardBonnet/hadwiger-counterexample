import Lax342547.ListTails
import Mathlib.Data.List.Sort

namespace Lax342547Proofs.ListTails
open Lax342547.ListTails

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/--
---
conclusion: Lax342547.ListTails.value_in_range
---
-/
theorem value_in_range (l : List ℝ) (t : ℕ) (ht : t < l.length) : value l t = l[t] := by
  simp [value,List.getElem?_eq_getElem ht]

/--
---
conclusion: Lax342547.ListTails.value_out_of_range
---
-/
theorem value_out_of_range (l : List ℝ) (t : ℕ) (ht : l.length ≤ t) : value l t = 0 := by
  simp [value,List.getElem?_eq_none ht]

/--
---
conclusion: Lax342547.ListTails.value_nonneg
---
-/
theorem value_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 ≤ x) (t : ℕ) : 0 ≤ value l t := by
  by_cases ht : t < l.length
  · rw [Lax342547.ListTails.value_in_range l t ht]
    exact h _ (List.getElem_mem ht)
  · rw [Lax342547.ListTails.value_out_of_range l t (by omega)]

/--
---
conclusion: Lax342547.ListTails.value_antitone
---
-/
theorem value_antitone (l : List ℝ) (h : l.Pairwise (fun a b => b ≤ a))
    (h0 : ∀ x ∈ l, 0 ≤ x) : Antitone (value l) := by
  intro i j hij
  by_cases hj : j < l.length
  · have hi : i < l.length := by omega
    rw [Lax342547.ListTails.value_in_range l i hi,Lax342547.ListTails.value_in_range l j hj]
    rcases eq_or_lt_of_le hij with rfl | hij
    · exact le_rfl
    · exact (List.pairwise_iff_getElem.mp h) i j hi hj hij
  · rw [Lax342547.ListTails.value_out_of_range l j (by omega)]
    exact Lax342547.ListTails.value_nonneg l h0 i

/--
---
conclusion: Lax342547.ListTails.value_drop
---
-/
theorem value_drop (l : List ℝ) (n t : ℕ) : value (l.drop n) t = value l (n+t) := by
  simp [value,List.getElem?_drop]

/--
---
conclusion: Lax342547.ListTails.sum_values
---
-/
theorem sum_values (l : List ℝ) : (∑ t ∈ Finset.range l.length, value l t) = l.sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    simpa [value,add_comm] using congrArg (fun z : ℝ => z+x) ih

/--
---
conclusion: Lax342547.ListTails.tail_sum_list
---
-/
theorem tail_sum_list (l : List ℝ) (b : ℕ) (hb : b ≤ l.length) :
    Lax342547.DyadicTails.tailSum (value l) l.length b = (l.drop (l.length-b)).sum := by
  rw [← Lax342547.ListTails.sum_values]
  simp only [List.length_drop,Nat.sub_sub_self hb]
  unfold Lax342547.DyadicTails.tailSum
  apply Finset.sum_congr rfl
  intro t _
  exact (Lax342547.ListTails.value_drop l (l.length-b) t).symm

end Lax342547Proofs.ListTails
