import Lax342547.StarRouting

/-!
---
title: The fifteen-rank witness tester target
type: definition and theorem
---
Odd witness lists turn the ordinary target coefficients into the shared moment at each witness tag. Their at most seven atoms route at most fourteen ordered ordinary testers to any component. All shared stars consolidate into one ordered shared tester. The resulting rank at most 15r represents the exact tester target on the entire profile space.
-/

namespace Lax342547.TargetTesters

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.Atoms
open Lax342547.PairedWitnesses Lax342547.WitnessAtoms Lax342547.StarRouting

axiom ordinary_star_representation {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (D : Testers (k := k) (b := b) (degree := degree) hr) (t : Tag k)
    (x : Profile k n b degree) :
    (∑ e, matrixPair (starMatrix hr (fun d => ordinary d t) (fun _ => 1) e) (x.val e)) = D.aTag t x

noncomputable def sharedMatrix {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (coeff : Tag k → Binary) (e : Component (Tag k)) : Moment k n b degree :=
  (∑ t ∈ e.val, coeff t) • orderedTesterMatrix hr shared

axiom shared_matrix_rank {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (coeff : Tag k → Binary) (e : Component (Tag k)) :
    (sharedMatrix (b := b) (degree := degree) hr coeff e).rank ≤ r

axiom shared_matrix_representation {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (D : Testers (k := k) (b := b) (degree := degree) hr) (coeff : Tag k → Binary)
    (x : Profile k n b degree) :
    (∑ e, matrixPair (sharedMatrix (b := b) (degree := degree) hr coeff e) (x.val e)) =
      ∑ t, coeff t * D.bTag t x

axiom tester_coefficient {k n b degree r : ℕ} (hr : 2 * r ≤ n)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (v : Representation k n b degree) (hv : chiStar hr v = 1) (t : Tag k) :
    1 + D.role ((representationCut k n b degree).rangeRestrict v) +
      D.bTag t ((representationCut k n b degree).rangeRestrict v) =
      blockTester hr shared (v.val t)

noncomputable def testerTarget {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (v : Profile k n b degree) :
    Module.Dual Binary (Profile k n b degree) :=
  D.role + (Lax342547.GradientForm.form D.role D.aTag D.bTag 0) v

axiom tester_target_formula {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (v : Representation k n b degree) (hv : chiStar hr v = 1) (x : Profile k n b degree) :
    testerTarget D ((representationCut k n b degree).rangeRestrict v) x =
      (∑ t, blockTester hr shared (v.val t) * D.aTag t x) +
      ∑ t, D.aTag t ((representationCut k n b degree).rangeRestrict v) * D.bTag t x

axiom left_witness_cut {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (i z : Fin 2) :
    (representationCut k n b degree).rangeRestrict (leftRepresentation W i z) = leftWitness W i z

axiom left_shared_sum {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (i z : Fin 2) (f : Tag k → Binary) :
    (∑ t, blockTester hr shared ((leftRepresentation W i z).val t) * f t) =
      ∑ j, ((W.left i z j).numerical hr).summary none * f (W.left i z j).tag

noncomputable def witnessTesterMatrix {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) (i z : Fin 2)
    (e : Component (Tag k)) : Moment k n b degree :=
  (∑ j, ((W.left i z j).numerical hr).summary none •
    starMatrix hr (fun d => ordinary d (W.left i z j).tag) (fun _ => 1) e) +
  sharedMatrix hr (fun t => D.aTag t (leftWitness W i z)) e

axiom witness_tester_rank {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) (i z : Fin 2)
    (e : Component (Tag k)) : (witnessTesterMatrix W D i z e).rank ≤ 15 * r

axiom witness_tester_representation {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) (i z : Fin 2)
    (hodd : (∑ j, diagonalBit hr (W.left i z j)) = 1) (x : Profile k n b degree) :
    (∑ e, matrixPair (witnessTesterMatrix W D i z e) (x.val e)) =
      testerTarget D (leftWitness W i z) x

end Lax342547.TargetTesters
