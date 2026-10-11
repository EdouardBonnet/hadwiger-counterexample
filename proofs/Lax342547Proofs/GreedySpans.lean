import Lax342547.GreedySpans
import Lax342547Proofs.SpanDeficits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

namespace Lax342547Proofs.GreedySpans
open Lax342547.GreedySpans

set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/--
---
conclusion: Lax342547.GreedySpans.gain_nonneg
---
-/
theorem gain_nonneg {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W S : Submodule K V) : 0 ≤ gain W S := by
  have hh := Submodule.finrank_mono (show W ≤ W ⊔ S from le_sup_left)
  unfold gain
  exact sub_nonneg.mpr (by exact_mod_cast hh)

/--
---
conclusion: Lax342547.GreedySpans.gain_le_rank
---
-/
theorem gain_le_rank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W S : Submodule K V) : gain W S ≤ Module.finrank K S := by
  have hh := Submodule.finrank_add_le_finrank_add_finrank W S
  unfold gain
  have hr : (Module.finrank K (W ⊔ S : Submodule K V) : ℝ) ≤ Module.finrank K W+Module.finrank K S := by exact_mod_cast hh
  linarith

/--
---
conclusion: Lax342547.GreedySpans.gain_antitone
---
-/
theorem gain_antitone {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W U : Submodule K V} (hWU : W ≤ U) (S : Submodule K V) :
    gain U S ≤ gain W S := by
  have hw := Submodule.finrank_sup_add_finrank_inf_eq W S
  have hu := Submodule.finrank_sup_add_finrank_inf_eq U S
  have hi := Submodule.finrank_mono (inf_le_inf_right S hWU)
  have hw' : (Module.finrank K (W ⊔ S : Submodule K V) : ℝ)+Module.finrank K (W ⊓ S : Submodule K V) = Module.finrank K W+Module.finrank K S := by exact_mod_cast hw
  have hu' : (Module.finrank K (U ⊔ S : Submodule K V) : ℝ)+Module.finrank K (U ⊓ S : Submodule K V) = Module.finrank K U+Module.finrank K S := by exact_mod_cast hu
  have hi' : (Module.finrank K (W ⊓ S : Submodule K V) : ℝ) ≤ Module.finrank K (U ⊓ S : Submodule K V) := by exact_mod_cast hi
  unfold gain
  linarith

/--
---
conclusion: Lax342547.GreedySpans.exists_greedy_order
---
-/
theorem exists_greedy_order {K V ι : Type} [Field K] [DecidableEq ι] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (I : Finset ι) (W : Submodule K V) :
    ∃ l : List ι, l.Nodup ∧ l.toFinset = I ∧ Greedy S W l := by
  classical
  revert W
  refine Finset.strongInductionOn I ?_
  intro I ih W
  by_cases hI : I.Nonempty
  · obtain ⟨i,hi,hmax⟩ := I.exists_max_image (fun j => gain W (S j)) hI
    obtain ⟨l,hn,hl,hg⟩ := ih (I.erase i) (Finset.erase_ssubset hi) (W ⊔ S i)
    refine ⟨i::l,?_,?_,?_,hg⟩
    · simp only [List.nodup_cons]
      exact ⟨by simp [← List.mem_toFinset,hl],hn⟩
    · simp only [List.toFinset_cons,hl,Finset.insert_erase hi]
    · intro j hj
      exact hmax j (Finset.mem_of_mem_erase (hl ▸ List.mem_toFinset.mpr hj))
  · refine ⟨[],by simp,?_,trivial⟩
    simpa using (Finset.not_nonempty_iff_eq_empty.mp hI).symm

/--
---
conclusion: Lax342547.GreedySpans.increments_length
---
-/
theorem increments_length {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    (increments S W l).length = l.length := by
  induction l generalizing W with
  | nil => rfl
  | cons i l ih => simp [increments,ih]

/--
---
conclusion: Lax342547.GreedySpans.span_after_eq
---
-/
theorem span_after_eq {K V ι : Type} [Field K] [DecidableEq ι] [AddCommGroup V] [Module K V]
    (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    spanAfter S W l = W ⊔ l.toFinset.sup S := by
  induction l generalizing W with
  | nil => simp [spanAfter]
  | cons i l ih => rw [spanAfter,ih,List.toFinset_cons,Finset.sup_insert,sup_assoc]

/--
---
conclusion: Lax342547.GreedySpans.increments_sum
---
-/
theorem increments_sum {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    (increments S W l).sum = (Module.finrank K (spanAfter S W l) : ℝ)-Module.finrank K W := by
  induction l generalizing W with
  | nil => simp [increments,spanAfter]
  | cons i l ih => simp only [increments,List.sum_cons,ih,spanAfter,gain]; ring

/--
---
conclusion: Lax342547.GreedySpans.increments_le
---
-/
theorem increments_le {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) (a : ℝ)
    (h : ∀ i ∈ l, gain W (S i) ≤ a) : ∀ x ∈ increments S W l, x ≤ a := by
  induction l generalizing W with
  | nil => simp [increments]
  | cons i l ih =>
    intro x hx
    simp only [increments,List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h i (by simp)
    · apply ih (W ⊔ S i) (fun j hj => (gain_antitone le_sup_left (S j)).trans (h j (by simp [hj]))) x hx

/--
---
conclusion: Lax342547.GreedySpans.increments_nonneg
---
-/
theorem increments_nonneg {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) :
    ∀ x ∈ increments S W l, 0 ≤ x := by
  induction l generalizing W with
  | nil => simp [increments]
  | cons i l ih =>
    intro x hx
    simp only [increments,List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact gain_nonneg _ _
    · exact ih _ x hx

/--
---
conclusion: Lax342547.GreedySpans.greedy_decreasing
---
-/
theorem greedy_decreasing {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (h : Greedy S W l) : (increments S W l).Pairwise (fun a b => b ≤ a) := by
  induction l generalizing W with
  | nil => simp [increments]
  | cons i l ih =>
    rw [increments,List.pairwise_cons]
    exact ⟨increments_le S (W ⊔ S i) l _
      (fun j hj => (gain_antitone le_sup_left (S j)).trans (h.1 j hj)),ih _ h.2⟩

/--
---
conclusion: Lax342547.GreedySpans.greedy_drop
---
-/
theorem greedy_drop {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι)
    (h : Greedy S W l) (n : ℕ) : Greedy S (spanAfter S W (l.take n)) (l.drop n) := by
  induction n generalizing W l with
  | zero => simpa [spanAfter] using h
  | succ n ih =>
    cases l with
    | nil => trivial
    | cons i l => simpa [List.take_succ_cons,List.drop_succ_cons,spanAfter] using ih (W ⊔ S i) l h.2

/--
---
conclusion: Lax342547.GreedySpans.increments_drop
---
-/
theorem increments_drop {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : ι → Submodule K V) (W : Submodule K V) (l : List ι) (n : ℕ) :
    (increments S W l).drop n = increments S (spanAfter S W (l.take n)) (l.drop n) := by
  induction n generalizing W l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons i l => simpa [increments,List.take_succ_cons,List.drop_succ_cons,spanAfter] using ih (W ⊔ S i) l

end Lax342547Proofs.GreedySpans
