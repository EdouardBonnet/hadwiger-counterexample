import Lax342547.ConcreteGeometry
import Lax342547.RawFrames

/-!
---
title: Concrete cut-space testers and the ordered mixer form
type: definition and theorem
---
The profile space is the image of the restricted cut map. The tester
functionals descend from actual allowed moment representatives. The
mixer sum retains the ordered component indices e,f in equation (2.9).
-/

namespace Lax342547.ConcreteCut

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles

noncomputable instance (k : ℕ) : Fintype (Component (Tag k)) := by
  classical
  exact inferInstanceAs (Fintype {e : Finset (Tag k) // e.card = 2})

noncomputable instance (k : ℕ) : DecidableEq (Component (Tag k)) := Classical.decEq _

def tagSpace (k n b degree : ℕ) (l : Tag k) : Submodule Binary (Moment k n b degree) :=
  momentSpace selectorEval (allowedBase k n l)

abbrev Representation (k n b degree : ℕ) := representatives (tagSpace k n b degree)

def representationCut (k n b degree : ℕ) :
    Representation k n b degree →ₗ[Binary] (Component (Tag k) → Moment k n b degree) :=
  cutMap.comp (representatives (tagSpace k n b degree)).subtype

abbrev Profile (k n b degree : ℕ) := LinearMap.range (representationCut k n b degree)

def representativeAt {k n b degree : ℕ} (l : Tag k) :
    Representation k n b degree →ₗ[Binary] Moment k n b degree :=
  (LinearMap.proj l).comp (representatives (tagSpace k n b degree)).subtype

def ordinarySum {k n b degree r : ℕ} (hr : 2 * r ≤ n) (t : Tag k) :
    Representation k n b degree →ₗ[Binary] Binary :=
  ∑ l : Tag k, ∑ d : Tag k, (blockTester hr (ordinary d t)).comp (representativeAt l)

noncomputable def sharedSum {k n b degree r : ℕ} (hr : 2 * r ≤ n) (t : Tag k) :
    Representation k n b degree →ₗ[Binary] Binary := by
  classical
  exact ∑ l ∈ Finset.univ.erase t, (blockTester hr shared).comp (representativeAt l)

/-- Unlike a and b, this quantity belongs to a specified representation. -/
def chiStar {k n b degree r : ℕ} (hr : 2 * r ≤ n) :
    Representation k n b degree →ₗ[Binary] Binary :=
  ∑ l : Tag k, (eta hr).comp (representativeAt l)

structure Testers {k n b degree r : ℕ} (hr : 2 * r ≤ n) where
  aTag : Tag k → Profile k n b degree →ₗ[Binary] Binary
  bTag : Tag k → Profile k n b degree →ₗ[Binary] Binary
  ordinary_formula : ∀ t w, aTag t ((representationCut k n b degree).rangeRestrict w) = ordinarySum hr t w
  shared_formula : ∀ t w, bTag t ((representationCut k n b degree).rangeRestrict w) = sharedSum hr t w

def Testers.role {k n b degree r : ℕ} {hr : 2 * r ≤ n} (D : Testers (k := k) (b := b) (degree := degree) hr) :
    Profile k n b degree →ₗ[Binary] Binary := ∑ t, D.aTag t

def profileAt {k n b degree : ℕ} (e : Component (Tag k)) :
    Profile k n b degree →ₗ[Binary] Moment k n b degree :=
  (LinearMap.proj e).comp (LinearMap.range (representationCut k n b degree)).subtype

def matrixPairing {I : Type} [Fintype I] : LinearMap.BilinForm Binary (Matrix I I Binary) where
  toFun := matrixPair
  map_add' x y := by
    ext w
    simp [matrixPair, Matrix.add_apply, add_smul, Finset.sum_add_distrib, LinearMap.sum_apply]
  map_smul' a x := by
    ext w
    simp [matrixPair, Matrix.smul_apply, mul_smul, Finset.smul_sum, LinearMap.sum_apply]

noncomputable def mixingForm {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) :
    LinearMap.BilinForm Binary (Profile k n b degree) :=
  ∑ j, ∑ e, ∑ f, matrixPairing.comp (profileAt e)
    ((RawFrames.sandwich (L j e f) (R j e f)).comp (profileAt f))

noncomputable def gradient {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) :
    LinearMap.BilinForm Binary (Profile k n b degree) :=
  GradientForm.form D.role D.aTag D.bTag (mixingForm L R)

axiom exists_testers {k n b degree r : ℕ} (hr : 2 * r ≤ n) :
    Nonempty (Testers (k := k) (b := b) (degree := degree) hr)

axiom gradient_properties {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree) :
    (∀ x y, gradient D L R x y = gradient D L R y x) ∧
      ∀ x, gradient D L R x x = D.role x

end Lax342547.ConcreteCut
