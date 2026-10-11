import Lax342547.Atoms
import Lax342547.BinaryPrescriptions

/-!
---
title: Witness atoms and their numerical tester records
type: lemma
---
A witness atom includes an actual allowed base vector and selector label.
Its numerical record keeps only the tag and tester summary. These records
determine the tester part of every atom-pair gradient entry.
-/

namespace Lax342547.WitnessAtoms

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.Atoms

structure PointAtom (k n b degree : ℕ) where
  tag : Tag k
  label : Fin b → Binary
  base : Base k n → Binary
  supported : ∀ i, i ∉ allowedBase k n tag → base i = 0

def PointAtom.vector {k n b degree : ℕ} (x : PointAtom k n b degree) : Vector k n b degree :=
  point selectorEval x.label x.base

noncomputable def PointAtom.profile {k n b degree : ℕ} (x : PointAtom k n b degree) :
    Profile k n b degree := atom x.tag x.label x.base x.supported

structure Numerical (k : ℕ) where
  tag : Tag k
  summary : Option (Tag k × Tag k) → Binary

def PointAtom.numerical {k n b degree r : ℕ} (hr : 2 * r ≤ n) (x : PointAtom k n b degree) :
    Numerical k := ⟨x.tag, testerSummary (degree := degree) hr x.label x.base⟩

def Numerical.aTag {k : ℕ} (x : Numerical k) (t : Tag k) : Binary :=
  ∑ d, x.summary (some (d, t))

def Numerical.bTag {k : ℕ} (x : Numerical k) (t : Tag k) : Binary :=
  if x.tag = t then 0 else x.summary none

def Numerical.role {k : ℕ} (x : Numerical k) : Binary := ∑ t, x.aTag t

def testerEntry {k : ℕ} (x y : Numerical k) : Binary :=
  x.role * y.role + ∑ t, (x.aTag t * y.bTag t + x.bTag t * y.aTag t)

abbrev ProductIndex (k J : ℕ) := Fin J × Lax342547.CutProfiles.Component (Tag k) ×
  Lax342547.CutProfiles.Component (Tag k)

def allowedIndex {k J : ℕ} (x y : Numerical k) (t : ProductIndex k J) : Prop :=
  x.tag ∈ t.2.1.val ∧ y.tag ∈ t.2.2.val

axiom tester_properties {k : ℕ} :
    (∀ x y : Numerical k, testerEntry x y = testerEntry y x) ∧
      ∀ x : Numerical k, testerEntry x x = x.role

axiom atom_testers {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (x : PointAtom k n b degree) :
    D.role x.profile = (x.numerical hr).role ∧
      (∀ t, D.aTag t x.profile = (x.numerical hr).aTag t) ∧
      ∀ t, D.bTag t x.profile = (x.numerical hr).bTag t

axiom allowed_index {k J : ℕ} (hk : 0 < k) (hJ : 0 < J) (x y : Numerical k) :
    ∃ t : ProductIndex k J, allowedIndex x y t

end Lax342547.WitnessAtoms
