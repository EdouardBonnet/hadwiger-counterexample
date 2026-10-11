import Lax342547.CutProfiles
import Mathlib.Tactic.Abel
import Lax342547.MomentIntersection

namespace Lax342547Proofs.CutProfiles

open Lax342547.MomentSpace Lax342547.CutProfiles

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

theorem cutMap_pair [DecidableEq Tag] (w : Tag → V) {i j : Tag} (h : i ≠ j) :
    cutMap w ⟨{i, j}, Finset.card_pair h⟩ = w i + w j := by
  simp [cutMap, h]

theorem binary_add_swap {a b c d : V} (h : a + b = c + d) : a + c = b + d := by
  have h' : a - c = d - b := sub_eq_sub_iff_add_eq_add.mpr (h.trans (add_comm c d))
  simpa [ZModModule.sub_eq_add, add_comm] using h'

theorem cutMap_eq_iff [Nonempty Tag] (w v : Tag → V) :
    cutMap w = cutMap v ↔ ∃ c, ∀ t, w t + v t = c := by
  classical
  constructor
  · intro h
    obtain ⟨t₀⟩ := ‹Nonempty Tag›
    refine ⟨w t₀ + v t₀, fun t => ?_⟩
    by_cases ht : t = t₀
    · subst t; rfl
    · have he := congrFun h ⟨{t, t₀}, Finset.card_pair ht⟩
      change (cutMap w) ⟨{t, t₀}, Finset.card_pair ht⟩ =
        (cutMap v) ⟨{t, t₀}, Finset.card_pair ht⟩ at he
      rw [cutMap_pair w ht, cutMap_pair v ht] at he
      exact binary_add_swap he
  · rintro ⟨c, hc⟩
    ext e
    obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp e.property
    have he' : e = ⟨{i, j}, Finset.card_pair hij⟩ := Subtype.ext he
    rw [he', cutMap_pair w hij, cutMap_pair v hij]
    exact binary_add_swap ((hc i).trans (hc j).symm)

/--
---
conclusion: Lax342547.CutProfiles.same_cut_iff
---
Equality in the coordinate for each tag pair forces the sums of the
two representative values to be constant. Subspace closure puts the
constant in every tag's allowed space. Conversely a constant tuple
contributes twice the same value to each cut, hence zero.
-/
theorem same_cut_iff [Nonempty Tag] (W : Tag → Submodule Binary V)
    (w v : Tag → V) (hw : ∀ t, w t ∈ W t) (hv : ∀ t, v t ∈ W t) :
    cutMap w = cutMap v ↔ ∃ c ∈ ⨅ t, W t, ∀ t, w t + v t = c := by
  rw [cutMap_eq_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_, hc⟩
    simp only [Submodule.mem_iInf]
    intro t
    rw [← hc t]
    exact (W t).add_mem (hw t) (hv t)
  · rintro ⟨c, _, hc⟩
    exact ⟨c, hc⟩

theorem same_moment_cut_iff {Label Coord Base : Type} [Nonempty Tag]
    (p : Label → Coord → Binary) (A : Tag → Set Base)
    (w v : Tag → Matrix (Coord × Option Base) (Coord × Option Base) Binary)
    (hw : ∀ t, w t ∈ momentSpace p (A t)) (hv : ∀ t, v t ∈ momentSpace p (A t)) :
    cutMap w = cutMap v ↔ ∃ c ∈ momentSpace p (⋂ t, A t), ∀ t, w t + v t = c := by
  rw [Lax342547.MomentIntersection.momentSpace_iInter]
  exact Lax342547.CutProfiles.same_cut_iff _ w v hw hv

end Lax342547Proofs.CutProfiles
