import Lax342547.GreedyTails
import Mathlib.Algebra.Order.BigOperators.Group.List
import Lax342547.DyadicScale
import Lax342547.GreedySpans
import Lax342547.ListTails

namespace Lax342547Proofs.GreedyTails
open Lax342547.GreedyTails

set_option backward.isDefEq.respectTransparency false
open Lax342547.GreedySpans Lax342547.ListTails Lax342547.DyadicTails
open scoped BigOperators

/--
---
conclusion: Lax342547.GreedyTails.greedy_deficit_bound
---
-/
theorem greedy_deficit_bound {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (hg : Greedy S W l) (hl : l ≠ []) :
    deficit S W l ≤ (l.length : ℝ)*value (increments S W l) 0-(increments S W l).sum := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons i l =>
    have hh : ∀ x ∈ (i::l).map (fun j => gain W (S j)), x ≤ gain W (S i) := by
      intro x hx
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
      rcases List.mem_cons.mp hj with rfl | hj
      · exact le_rfl
      · exact hg.1 j hj
    have hs := List.sum_le_card_nsmul ((i::l).map (fun j => gain W (S j))) (gain W (S i)) hh
    simp only [List.length_map,nsmul_eq_mul] at hs
    unfold deficit
    simpa only [increments,value,List.getElem?_cons_zero,Option.getD_some] using sub_le_sub_right hs _

/--
---
conclusion: Lax342547.GreedyTails.greedy_tail_bound
---
-/
theorem greedy_tail_bound {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (hg : Greedy S W l) (b : ℕ) (hb : 0 < b) (hbl : b ≤ l.length) :
    deficit S (spanAfter S W (l.take (l.length-b))) (l.drop (l.length-b)) ≤
      (b : ℝ)*tailDeficit (value (increments S W l)) l.length b := by
  let t := l.length-b
  have hlen : (l.drop t).length = b := by simp [t,List.length_drop,Nat.sub_sub_self hbl]
  have hne : l.drop t ≠ [] := by intro hh; rw [hh] at hlen; simp at hlen; omega
  have hh := Lax342547.GreedyTails.greedy_deficit_bound S (spanAfter S W (l.take t)) (l.drop t)
    (Lax342547.GreedySpans.greedy_drop S W l hg t) hne
  rw [← Lax342547.GreedySpans.increments_drop,hlen,
    Lax342547.ListTails.value_drop] at hh
  have hil := Lax342547.GreedySpans.increments_length S W l
  have hsum := Lax342547.ListTails.tail_sum_list (increments S W l) b (by omega)
  rw [hil] at hsum
  rw [← hsum] at hh
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have he : (b : ℝ)*tailDeficit (value (increments S W l)) l.length b =
      (b : ℝ)*value (increments S W l) (l.length-b)-tailSum (value (increments S W l)) l.length b := by
    unfold tailDeficit
    field_simp
  rw [he]
  exact hh

/--
---
conclusion: Lax342547.GreedyTails.small_greedy_tail
---
-/
theorem small_greedy_tail {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (hg : Greedy S W l) (r : ℝ) (hr : ∀ i ∈ l, (Module.finrank K (S i) : ℝ) ≤ r)
    (k n : ℕ) (hlen : l.length = 2^k) (hnk : n ≤ k) (hn : 8*r < n) :
    ∃ j < n, deficit S (spanAfter S W (l.take (l.length-2^(k-j))))
      (l.drop (l.length-2^(k-j))) < (2^(k-j) : ℝ)/4 := by
  let a := value (increments S W l)
  have ha := Lax342547.ListTails.value_antitone (increments S W l)
    (Lax342547.GreedySpans.greedy_decreasing S W l hg)
    (Lax342547.GreedySpans.increments_nonneg S W l)
  have h0 := fun t => Lax342547.ListTails.value_nonneg (increments S W l)
    (Lax342547.GreedySpans.increments_nonneg S W l) t
  have hbnd := Lax342547.GreedySpans.increments_le S W l r
    (fun i hi => (Lax342547.GreedySpans.gain_le_rank W (S i)).trans (hr i hi))
  have hlen' := Lax342547.GreedySpans.increments_length S W l
  have hz : 0 < (increments S W l).length := by rw [hlen',hlen]; positivity
  have har : a 0 ≤ r := by
    dsimp [a]
    rw [Lax342547.ListTails.value_in_range _ 0 hz]
    exact hbnd _ (List.getElem_mem hz)
  obtain ⟨j,hj,hd⟩ := Lax342547.DyadicScale.dyadic_small_tail a ha h0 k n r hnk har hn
  refine ⟨j,hj,?_⟩
  have hbl : (2 : ℕ)^(k-j) ≤ l.length := by
    rw [hlen]
    exact Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hh := Lax342547.GreedyTails.greedy_tail_bound S W l hg (2^(k-j)) (by positivity) hbl
  rw [hlen] at hh
  have hp : (0 : ℝ) < 2^(k-j) := by positivity
  have hmul := mul_lt_mul_of_pos_left hd hp
  push_cast at hh
  rw [hlen]
  calc
    _ ≤ (2^(k-j) : ℝ)*tailDeficit a (2^k) (2^(k-j)) := hh
    _ < (2^(k-j) : ℝ)/4 := by
      simpa only [mul_one_div] using hmul

end Lax342547Proofs.GreedyTails
