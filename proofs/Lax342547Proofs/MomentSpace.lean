import Lax342547.MomentIntersection
import Mathlib.Tactic.Ring

namespace Lax342547Proofs.MomentSpace

open Lax342547.MomentSpace

variable {Label Coord Base : Type} (p : Label → Coord → Binary)

theorem pointMoment_mem (A : Set Base) (s : Label) (z : Base → Binary)
    (hz : ∀ i, i ∉ A → z i = 0) : pointMoment p s z ∈ momentSpace p A :=
  Submodule.subset_span ⟨s, z, hz, rfl⟩

theorem momentSpace_mono {A B : Set Base} (h : A ⊆ B) :
    momentSpace p A ≤ momentSpace p B := by
  apply Submodule.span_le.mpr
  rintro w ⟨s, z, hz, rfl⟩
  exact pointMoment_mem p B s z (fun i hi => hz i (fun hia => hi (h hia)))

theorem point_erase (A : Set Base) (s : Label) (z : Base → Binary)
    (i : Coord × Option Base) :
    point p s (eraseBase A z) i = mask A i * point p s z i := by
  classical
  rcases i with ⟨c, _ | b⟩
  · simp [point, baseEval, mask, allowed]
  · by_cases hb : b ∈ A <;> simp [point, baseEval, mask, allowed, eraseBase, hb]

theorem project_pointMoment (A : Set Base) (s : Label) (z : Base → Binary) :
    project A (pointMoment p s z) = pointMoment p s (eraseBase A z) := by
  ext i j
  change mask A i * (point p s z i * point p s z j) * mask A j =
    point p s (eraseBase A z) i * point p s (eraseBase A z) j
  rw [point_erase, point_erase]
  ring

theorem project_mem (A : Set Base) {w} (hw : w ∈ momentSpace p Set.univ) :
    project A w ∈ momentSpace p A := by
  classical
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, z, _, rfl⟩ := hw
    rw [project_pointMoment]
    exact pointMoment_mem p A s _ (by intro i hi; simp [eraseBase, hi])
  | zero => simp
  | add w v _ _ hw hv => simpa using (momentSpace p A).add_mem hw hv
  | smul c w _ hw => simpa using (momentSpace p A).smul_mem c hw

theorem point_zero_of_not_allowed {A : Set Base} {s : Label} {z : Base → Binary}
    (hz : ∀ i, i ∉ A → z i = 0) {i : Coord × Option Base} (hi : ¬allowed A i) :
    point p s z i = 0 := by
  rcases i with ⟨c, _ | b⟩
  · exact (hi trivial).elim
  · simp [point, baseEval, hz b hi]

theorem entries_zero {A : Set Base} {w} (hw : w ∈ momentSpace p A)
    (i j : Coord × Option Base) (hij : ¬allowed A i ∨ ¬allowed A j) : w i j = 0 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, z, hz, rfl⟩ := hw
    rcases hij with hi | hj
    · simp [pointMoment, point_zero_of_not_allowed p hz hi]
    · simp [pointMoment, point_zero_of_not_allowed p hz hj]
  | zero => rfl
  | add w v _ _ hw hv => simp [Matrix.add_apply, hw, hv]
  | smul c w _ hw => simp [Matrix.smul_apply, hw]

theorem project_eq_self {A : Set Base}
    {w : Matrix (Coord × Option Base) (Coord × Option Base) Binary}
    (hw : ∀ i j, ¬allowed A i ∨ ¬allowed A j → w i j = 0) : project A w = w := by
  classical
  ext i j
  change mask A i * w i j * mask A j = w i j
  by_cases hi : allowed A i <;> by_cases hj : allowed A j
  · simp [mask, hi, hj]
  · simp [mask, hi, hj, hw i j (Or.inr hj)]
  · simp [mask, hi, hj, hw i j (Or.inl hi)]
  · simp [mask, hi, hj, hw i j (Or.inl hi)]

theorem mem_iff {A : Set Base} {w : Matrix _ _ Binary} :
    w ∈ momentSpace p A ↔ w ∈ momentSpace p Set.univ ∧
      ∀ i j, ¬allowed A i ∨ ¬allowed A j → w i j = 0 := by
  constructor
  · intro hw
    exact ⟨momentSpace_mono p (Set.subset_univ _) hw, entries_zero p hw⟩
  · rintro ⟨hw, hz⟩
    rw [← project_eq_self hz]
    exact project_mem p A hw

theorem allowed_iInter {Tag : Type} (A : Tag → Set Base) (i : Coord × Option Base) :
    allowed (⋂ t, A t) i ↔ ∀ t, allowed (A t) i := by
  rcases i with ⟨c, _ | b⟩ <;> simp [allowed]

/--
---
conclusion: Lax342547.MomentIntersection.momentSpace_iInter
---
A matrix in the intersection has a zero entry whenever either coordinate
is forbidden by any restriction. Projecting all its point generators onto
the intersection of the allowed base coordinates fixes that matrix.
-/
theorem momentSpace_iInter {Tag : Type} [Nonempty Tag] (A : Tag → Set Base) :
    momentSpace p (⋂ t, A t) = ⨅ t, momentSpace p (A t) := by
  classical
  apply le_antisymm
  · exact le_iInf (fun t => momentSpace_mono p (Set.iInter_subset A t))
  · intro w hw
    have hmem : ∀ t, w ∈ momentSpace p (A t) := by simpa using hw
    obtain ⟨t⟩ := ‹Nonempty Tag›
    apply (mem_iff p).mpr
    refine ⟨momentSpace_mono p (Set.subset_univ _) (hmem t), ?_⟩
    intro i j hij
    simp only [allowed_iInter, not_forall] at hij
    rcases hij with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact entries_zero p (hmem s) i j (Or.inl hs)
    · exact entries_zero p (hmem s) i j (Or.inr hs)

end Lax342547Proofs.MomentSpace
