import Lax342547.TagGeometry
import Lax342547Proofs.CutProfiles
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.TagGeometry

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.CutProfiles

theorem interval_card_le (k : ℕ) (d : Tag k) : (interval k d).card ≤ k := by
  exact (Finset.card_image_le).trans (by simp)

theorem exists_disallowing (k : ℕ) (S : Finset (Tag k)) (hS : k < S.card) (d : Tag k) :
    ∃ l ∈ S, l ∉ interval k d := by
  classical
  by_contra h
  push Not at h
  have hc := (Finset.card_le_card h).trans (interval_card_le k d)
  omega

theorem majority_allowed (k n : ℕ) (S : Finset (Tag k)) (hS : k < S.card) :
    (⋂ l : {l // l ∈ S}, allowedBase k n l.val) = commonBase k n := by
  ext c
  simp only [Set.mem_iInter]
  rcases c with ⟨⟨d, t⟩, i⟩ | ⟨b, i⟩
  · change (∀ l : {l // l ∈ S}, l.val ∈ interval k d) ↔ False
    obtain ⟨l, hl, hd⟩ := exists_disallowing k S hS d
    exact ⟨fun h => hd (h ⟨l, hl⟩), False.elim⟩
  · exact ⟨fun _ => trivial, fun _ _ => trivial⟩

/--
---
conclusion: Lax342547.TagGeometry.majority_intersection
---
Each ordinary block is allowed at at most k tags. A set of more than k
tags therefore forbids each ordinary block somewhere. The coordinate
projection theorem identifies the resulting intersection of moment spaces.
-/
theorem majority_intersection {Label Coord : Type} (k n : ℕ)
    (p : Label → Coord → Binary) (S : Finset (Tag k)) (hS : k < S.card) :
    (⨅ l : {l // l ∈ S}, momentSpace p (allowedBase k n l.val)) =
      momentSpace p (commonBase k n) := by
  classical
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have : Nonempty {l // l ∈ S} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  rw [← MomentSpace.momentSpace_iInter, majority_allowed k n S hS]

theorem all_tag_intersection {Label Coord : Type} (k n : ℕ)
    (p : Label → Coord → Binary) :
    (⨅ l : Tag k, momentSpace p (allowedBase k n l)) = momentSpace p (commonBase k n) := by
  classical
  have h := majority_intersection k n p Finset.univ (by simp [ZMod.card]; omega)
  ext w
  rw [← h]
  simp only [Submodule.mem_iInf]
  exact ⟨fun hw l => hw l.val, fun hw l => hw ⟨l, Finset.mem_univ l⟩⟩

theorem same_cut_common_constant {Label Coord : Type} (k n : ℕ)
    (p : Label → Coord → Binary)
    (w v : Tag k → Matrix (Coord × Option (Base k n)) (Coord × Option (Base k n)) Binary)
    (hw : ∀ t, w t ∈ momentSpace p (allowedBase k n t))
    (hv : ∀ t, v t ∈ momentSpace p (allowedBase k n t)) :
    cutMap w = cutMap v ↔ ∃ c ∈ momentSpace p (commonBase k n), ∀ t, w t + v t = c := by
  rw [← all_tag_intersection k n p]
  exact CutProfiles.same_cut_iff _ w v hw hv

end Lax342547Proofs.TagGeometry
