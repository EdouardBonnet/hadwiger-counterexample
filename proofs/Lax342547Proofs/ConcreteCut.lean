import Lax342547.ConcreteCut
import Lax342547Proofs.ConcreteGeometry
import Lax342547Proofs.TagGeometry
import Lax342547Proofs.CutFunctionals

namespace Lax342547Proofs.ConcreteCut

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.ConcreteCut

variable {k n b degree r : ℕ}

theorem profile_eq_cutSpace :
    LinearMap.range (representationCut k n b degree) = cutSpace (tagSpace k n b degree) := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.val, w.property, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

theorem representative_mem (w : Representation k n b degree) (l : Tag k) :
    w.val l ∈ tagSpace k n b degree l := w.property l trivial

theorem ordinarySum_apply (hr : 2 * r ≤ n) (t : Tag k) (w : Representation k n b degree) :
    ordinarySum hr t w = ∑ l : Tag k, ∑ d : Tag k, blockTester hr (ordinary d t) (w.val l) := by
  simp [ordinarySum, representativeAt, LinearMap.sum_apply]

theorem sharedSum_apply (hr : 2 * r ≤ n) (t : Tag k) (w : Representation k n b degree) :
    sharedSum hr t w = ∑ l ∈ Finset.univ.erase t, blockTester hr shared (w.val l) := by
  classical
  simp [sharedSum, representativeAt, LinearMap.sum_apply]

theorem representative_testers_eq (hr : 2 * r ≤ n) (t : Tag k)
    (w v : Representation k n b degree) (heq : representationCut k n b degree w = representationCut k n b degree v) :
    ordinarySum hr t w = ordinarySum hr t v ∧ sharedSum hr t w = sharedSum hr t v := by
  classical
  have hO : ∀ c ∈ ⨅ l, tagSpace k n b degree l,
      (∑ d : Tag k, blockTester hr (ordinary d t)) c = 0 := by
    intro c hc
    have hc' : c ∈ momentSpace selectorEval (commonBase k n) := by
      change c ∈ ⨅ l : Tag k, momentSpace (selectorEval (degree := degree)) (allowedBase k n l) at hc
      rwa [TagGeometry.all_tag_intersection] at hc
    simp only [LinearMap.sum_apply]
    exact Finset.sum_eq_zero (fun d _ => ConcreteGeometry.ordinaryTester_common_zero hr d t hc')
  have hodd : Odd (Fintype.card (Tag k)) := by
    rw [ZMod.card]
    exact ⟨k, rfl⟩
  have he := CutFunctionals.representative_sums_eq (tagSpace k n b degree)
    (∑ d : Tag k, blockTester hr (ordinary d t)) (blockTester hr shared) hO hodd
    w.val v.val (representative_mem w) (representative_mem v) heq
  exact ⟨by simpa [ordinarySum_apply, LinearMap.sum_apply] using he.1,
    by simpa only [sharedSum_apply] using he.2 t⟩

/--
---
conclusion: Lax342547.ConcreteCut.exists_testers
---
Ordinary testers vanish on the common moment space. Shared testers are
summed over an even number of tags. The checked cut-kernel theorem gives
representative independence, and quotient descent constructs the actual
linear functionals on the image of the restricted cut map.
-/
theorem exists_testers (hr : 2 * r ≤ n) :
    Nonempty (Testers (k := k) (b := b) (degree := degree) hr) := by
  classical
  have hO (t : Tag k) : LinearMap.ker (representationCut k n b degree) ≤ LinearMap.ker (ordinarySum hr t) := by
    intro w hw
    have he : representationCut k n b degree w = representationCut k n b degree 0 := by
      simpa only [map_zero] using LinearMap.mem_ker.mp hw
    simpa only [map_zero, LinearMap.mem_ker] using (representative_testers_eq hr t w 0 he).1
  have hS (t : Tag k) : LinearMap.ker (representationCut k n b degree) ≤ LinearMap.ker (sharedSum hr t) := by
    intro w hw
    have he : representationCut k n b degree w = representationCut k n b degree 0 := by
      simpa only [map_zero] using LinearMap.mem_ker.mp hw
    simpa only [map_zero, LinearMap.mem_ker] using (representative_testers_eq hr t w 0 he).2
  exact ⟨{
    aTag := fun t => CutFunctionals.descend _ (ordinarySum hr t) (hO t)
    bTag := fun t => CutFunctionals.descend _ (sharedSum hr t) (hS t)
    ordinary_formula := fun t w => CutFunctionals.descend_apply _ _ (hO t) w
    shared_formula := fun t w => CutFunctionals.descend_apply _ _ (hS t) w }⟩

theorem mixingForm_apply {J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (x y : Profile k n b degree) :
    mixingForm L R x y = ∑ j, ∑ e, ∑ f, matrixPair (x.val e) (L j e f * y.val f * (R j e f).transpose) := by
  simp [mixingForm, matrixPairing, profileAt, Lax342547.RawFrames.sandwich, LinearMap.sum_apply]

theorem role_formula {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (w : Representation k n b degree) :
    D.role ((representationCut k n b degree).rangeRestrict w) = ∑ l : Tag k, etaO hr (w.val l) := by
  simp only [Testers.role, LinearMap.sum_apply, D.ordinary_formula, ordinarySum_apply, etaO]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  exact Finset.sum_comm

/--
---
conclusion: Lax342547.ConcreteCut.gradient_properties
---
Instantiate the proved binary symmetrization identity with the descended
testers and the actual ordered-component mixer sum.
-/
theorem gradient_properties {J : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) :
    (∀ x y, gradient D L R x y = gradient D L R y x) ∧
      ∀ x, gradient D L R x x = D.role x :=
  GradientForm.form_properties D.role D.aTag D.bTag (mixingForm L R)

end Lax342547Proofs.ConcreteCut
