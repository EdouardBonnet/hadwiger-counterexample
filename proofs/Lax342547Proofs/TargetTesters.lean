import Lax342547.TargetTesters
import Lax342547.PairedWitnesses
import Lax342547.StarRouting
import Lax342547Proofs.ConcreteCut
import Lax342547Proofs.GradientForm

namespace Lax342547Proofs.TargetTesters
open Lax342547.TargetTesters

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.Atoms
open Lax342547.PairedWitnesses Lax342547.WitnessAtoms Lax342547.StarRouting

/--
---
conclusion: Lax342547.TargetTesters.ordinary_star_representation
---
-/
theorem ordinary_star_representation {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (D : Testers (k := k) (b := b) (degree := degree) hr) (t : Tag k)
    (x : Profile k n b degree) :
    (∑ e, matrixPair (starMatrix hr (fun d => ordinary d t) (fun _ => 1) e) (x.val e)) = D.aTag t x := by
  classical
  obtain ⟨w, hw⟩ := x.property
  have hx : (representationCut k n b degree).rangeRestrict w = x := Subtype.ext hw
  subst x
  have h := Lax342547.StarRouting.star_matrix_representation hr (fun d => ordinary d t) (fun _ => 1) w
  simp only [one_mul] at h
  change (∑ e, matrixPair (starMatrix hr (fun d => ordinary d t) (fun _ => 1) e)
    ((representationCut k n b degree w) e)) = _
  rw [h]
  rw [D.ordinary_formula, Lax342547Proofs.ConcreteCut.ordinarySum_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have hz := Lax342547.StarRouting.ordinary_tester_disallowed_zero hr d t d
    (Lax342547.StarRouting.interval_center_excluded d) w
  have hsub := Finset.sum_subtype (F := inferInstance) (p := fun l : Tag k => l ≠ d)
    (Finset.univ.erase d) (by simp) (fun l => blockTester hr (ordinary d t) (w.val l))
  rw [← hsub]
  simpa only [hz, add_zero] using (Finset.sum_erase_add Finset.univ
    (fun l => blockTester hr (ordinary d t) (w.val l)) (Finset.mem_univ d))

/--
---
conclusion: Lax342547.TargetTesters.shared_matrix_rank
---
-/
theorem shared_matrix_rank {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (coeff : Tag k → Binary) (e : Component (Tag k)) :
    (sharedMatrix (b := b) (degree := degree) hr coeff e).rank ≤ r := by
  exact (Lax342547.StarRouting.matrix_smul_rank _ _).trans
    (Lax342547.StarRouting.ordered_tester_rank hr shared)

/--
---
conclusion: Lax342547.TargetTesters.shared_matrix_representation
---
-/
theorem shared_matrix_representation {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (D : Testers (k := k) (b := b) (degree := degree) hr) (coeff : Tag k → Binary)
    (x : Profile k n b degree) :
    (∑ e, matrixPair (sharedMatrix (b := b) (degree := degree) hr coeff e) (x.val e)) =
      ∑ t, coeff t * D.bTag t x := by
  classical
  obtain ⟨w, hw⟩ := x.property
  have hx : (representationCut k n b degree).rangeRestrict w = x := Subtype.ext hw
  subst x
  have he (e : Component (Tag k)) : sharedMatrix (b := b) (degree := degree) hr coeff e =
      starMatrix hr (fun _ => shared) coeff e := by
    simp only [sharedMatrix, starMatrix, Finset.sum_smul]
  simp only [he]
  change (∑ e, matrixPair (starMatrix hr (fun _ => shared) coeff e)
    ((representationCut k n b degree w) e)) = _
  rw [Lax342547.StarRouting.star_matrix_representation]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  rw [D.shared_formula, Lax342547Proofs.ConcreteCut.sharedSum_apply]
  exact (Finset.sum_subtype (F := inferInstance) (p := fun l : Tag k => l ≠ t)
    (Finset.univ.erase t) (by simp) (fun l => blockTester hr shared (w.val l))).symm

/--
---
conclusion: Lax342547.TargetTesters.tester_coefficient
---
-/
theorem tester_coefficient {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (v : Representation k n b degree) (hv : chiStar hr v = 1) (t : Tag k) :
    1 + D.role ((representationCut k n b degree).rangeRestrict v) +
      D.bTag t ((representationCut k n b degree).rangeRestrict v) =
      blockTester hr shared (v.val t) := by
  classical
  have ha := Lax342547Proofs.ConcreteCut.role_formula D v
  have hb := D.shared_formula t v
  rw [Lax342547Proofs.ConcreteCut.sharedSum_apply] at hb
  have hc : (∑ l, etaO hr (v.val l)) + (∑ l, blockTester hr shared (v.val l)) = 1 := by
    simpa only [chiStar, eta, LinearMap.sum_apply, LinearMap.add_apply,
      Finset.sum_add_distrib, representativeAt, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply] using hv
  have hs := Finset.sum_erase_add Finset.univ (fun l => blockTester hr shared (v.val l))
    (Finset.mem_univ t)
  rw [ha, hb]
  rw [← hc, ← hs]
  have hz (a : Binary) : a + a = 0 := ZModModule.add_self a
  abel_nf
  simp only [two_smul, hz, zero_add]



/--
---
conclusion: Lax342547.TargetTesters.tester_target_formula
---
-/
theorem tester_target_formula {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (v : Representation k n b degree) (hv : chiStar hr v = 1) (x : Profile k n b degree) :
    testerTarget D ((representationCut k n b degree).rangeRestrict v) x =
      (∑ t, blockTester hr shared (v.val t) * D.aTag t x) +
      ∑ t, D.aTag t ((representationCut k n b degree).rangeRestrict v) * D.bTag t x := by
  classical
  let y := (representationCut k n b degree).rangeRestrict v
  have he : testerTarget D y x = (1 + D.role y) * D.role x +
      ∑ t, (D.aTag t y * D.bTag t x + D.bTag t y * D.aTag t x) := by
    simp only [testerTarget, Lax342547.GradientForm.form, LinearMap.add_apply,
      LinearMap.sum_apply, Lax342547Proofs.GradientForm.rankOne_apply,
      LinearMap.BilinForm.flip, map_zero, add_zero]
    ring
  rw [he]
  have ha : D.role x = ∑ t, D.aTag t x := by simp [Testers.role, LinearMap.sum_apply]
  rw [ha, Finset.mul_sum, Finset.sum_add_distrib]
  have hc (t : Tag k) : (1 + D.role y) * D.aTag t x + D.bTag t y * D.aTag t x =
      blockTester hr shared (v.val t) * D.aTag t x := by
    rw [← add_mul]
    exact congrArg (fun a => a * D.aTag t x) (Lax342547.TargetTesters.tester_coefficient hr D v hv t)
  have hs : (∑ t, (1 + D.role y) * D.aTag t x) + (∑ t, D.bTag t y * D.aTag t x) =
      ∑ t, blockTester hr shared (v.val t) * D.aTag t x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun t _ => hc t)
  change _ = _ + ∑ t, D.aTag t y * D.bTag t x
  rw [← hs]
  abel

/--
---
conclusion: Lax342547.TargetTesters.left_witness_cut
---
-/
theorem left_witness_cut {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (i z : Fin 2) :
    (representationCut k n b degree).rangeRestrict (leftRepresentation W i z) = leftWitness W i z := by
  simp only [leftRepresentation, leftWitness, map_sum, PointAtom.profile, atom]

/--
---
conclusion: Lax342547.TargetTesters.left_shared_sum
---
-/
theorem left_shared_sum {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (i z : Fin 2) (f : Tag k → Binary) :
    (∑ t, blockTester hr shared ((leftRepresentation W i z).val t) * f t) =
      ∑ j, ((W.left i z j).numerical hr).summary none * f (W.left i z j).tag := by
  classical
  have ht (t : Tag k) : blockTester hr shared ((leftRepresentation W i z).val t) =
      ∑ j, if (W.left i z j).tag = t then ((W.left i z j).numerical hr).summary none else 0 := by
    simp only [leftRepresentation, Submodule.coe_sum, Finset.sum_apply, atomRepresentation]
    change blockTester hr shared (∑ j, (Pi.single (W.left i z j).tag
      (pointMoment selectorEval (W.left i z j).label (W.left i z j).base) : Tag k → Moment k n b degree) t) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : (W.left i z j).tag = t <;>
      simp [hj, PointAtom.numerical, testerSummary]
  simp only [ht, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul, eq_comm]

/--
---
conclusion: Lax342547.TargetTesters.witness_tester_rank
---
-/
theorem witness_tester_rank {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) (i z : Fin 2)
    (e : Component (Tag k)) : (witnessTesterMatrix W D i z e).rank ≤ 15 * r := by
  classical
  have hsum : (∑ j : Fin (W.length i z), ((W.left i z j).numerical hr).summary none •
      starMatrix (b := b) (degree := degree) hr
        (fun d => ordinary d (W.left i z j).tag) (fun _ => 1) e).rank ≤ 14 * r := by
    have h := Lax342547.StarRouting.matrix_sum_rank (fun j : Fin (W.length i z) =>
      ((W.left i z j).numerical hr).summary none • starMatrix (b := b) (degree := degree) hr
        (fun d => ordinary d (W.left i z j).tag) (fun _ => 1) e)
    have h' : (∑ j : Fin (W.length i z),
        (((W.left i z j).numerical hr).summary none • starMatrix (b := b) (degree := degree) hr
          (fun d => ordinary d (W.left i z j).tag) (fun _ => 1) e).rank) ≤ W.length i z * (2 * r) := by
      have hh : (∑ j : Fin (W.length i z),
          (((W.left i z j).numerical hr).summary none • starMatrix (b := b) (degree := degree) hr
            (fun d => ordinary d (W.left i z j).tag) (fun _ => 1) e).rank) ≤ ∑ _ : Fin (W.length i z), 2 * r :=
        Finset.sum_le_sum (fun j _ =>
        (Lax342547.StarRouting.matrix_smul_rank _ _).trans
          (Lax342547.StarRouting.star_matrix_rank (b := b) (degree := degree) hr
            (fun d => ordinary d (W.left i z j).tag) (fun _ => 1) e))
      simpa using hh
    exact (h.trans h').trans (by nlinarith [W.short i z])
  have h := Lax342547.StarRouting.matrix_add_rank (B := Coordinate k n b degree)
    (∑ j, ((W.left i z j).numerical hr).summary none •
      starMatrix hr (fun d => ordinary d (W.left i z j).tag) (fun _ => 1) e)
    (sharedMatrix hr (fun t => D.aTag t (leftWitness W i z)) e)
  have hs := Lax342547.TargetTesters.shared_matrix_rank (b := b) (degree := degree) hr (fun t => D.aTag t (leftWitness W i z)) e
  exact h.trans (by omega)



/--
---
conclusion: Lax342547.TargetTesters.witness_tester_representation
---
-/
theorem witness_tester_representation {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) (i z : Fin 2)
    (hodd : (∑ j, diagonalBit hr (W.left i z j)) = 1) (x : Profile k n b degree) :
    (∑ e, matrixPair (witnessTesterMatrix W D i z e) (x.val e)) =
      testerTarget D (leftWitness W i z) x := by
  classical
  have hv : chiStar hr (leftRepresentation W i z) = 1 :=
    (Lax342547.PairedWitnesses.diagonal_sums W i z).1.trans hodd
  have ht := Lax342547.TargetTesters.tester_target_formula D (leftRepresentation W i z) hv x
  rw [Lax342547.TargetTesters.left_witness_cut, Lax342547.TargetTesters.left_shared_sum] at ht
  rw [ht]
  change (∑ e, matrixPairing (witnessTesterMatrix W D i z e) (x.val e)) = _
  simp only [witnessTesterMatrix, map_add, map_sum, map_smul, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have he (j : Fin (W.length i z)) :
      (∑ e, ((W.left i z j).numerical hr).summary none *
        matrixPairing (starMatrix hr (fun d => ordinary d (W.left i z j).tag) (fun _ => 1) e) (x.val e)) =
      ((W.left i z j).numerical hr).summary none * D.aTag (W.left i z j).tag x := by
    rw [← Finset.mul_sum]
    congr 1
    exact Lax342547.TargetTesters.ordinary_star_representation hr D (W.left i z j).tag x
  simp only [he]
  congr 1
  exact Lax342547.TargetTesters.shared_matrix_representation hr D (fun t => D.aTag t (leftWitness W i z)) x

end Lax342547Proofs.TargetTesters
