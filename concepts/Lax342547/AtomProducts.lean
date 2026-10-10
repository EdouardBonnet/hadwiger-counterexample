import Lax342547.WitnessAtoms

/-!
---
title: Ordered atom products in the actual gradient form
type: definition and theorem
---
Atom-pair mixing is exactly the product sum indexed by the two incident
stars. Thus matching prescribed distinct-atom bits gives the prescribed
gradient entries. No claim of occurrence or independence of those bits
is part of this deterministic identity.
-/

namespace Lax342547.AtomProducts

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.WitnessAtoms
open Lax342547.BinaryPrescriptions

noncomputable def evaluatedBits {k n b degree J : ℕ}
    (M : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (x y : PointAtom k n b degree) (t : ProductIndex k J) : Binary := by
  classical
  exact if x.tag ∈ t.2.1.val ∧ y.tag ∈ t.2.2.val then
    (M t.1 t.2.1 t.2.2).toBilin' x.vector y.vector else 0

axiom mixing_atoms {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (x y : PointAtom k n b degree) :
    mixingForm L R x.profile y.profile = productSum (evaluatedBits L) (evaluatedBits R) x y

axiom gradient_atoms {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (x y : PointAtom k n b degree) :
    gradient D L R x.profile y.profile = testerEntry (x.numerical hr) (y.numerical hr) +
      productSum (evaluatedBits L) (evaluatedBits R) x y +
      productSum (evaluatedBits L) (evaluatedBits R) y x

axiom gradient_of_prescriptions {I : Type} {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (atoms : I → PointAtom k n b degree) (lbits rbits : I → I → ProductIndex k J → Binary)
    (hzero : ∀ x y t, ¬ allowedIndex ((atoms x).numerical hr) ((atoms y).numerical hr) t →
      lbits x y t = 0 ∧ rbits x y t = 0)
    (hbits : ∀ x y, x ≠ y → ∀ t,
      allowedIndex ((atoms x).numerical hr) ((atoms y).numerical hr) t →
      (L t.1 t.2.1 t.2.2).toBilin' (atoms x).vector (atoms y).vector = lbits x y t ∧
      (R t.1 t.2.1 t.2.2).toBilin' (atoms x).vector (atoms y).vector = rbits x y t) :
    ∀ x y, gradient D L R (atoms x).profile (atoms y).profile =
      testerEntry ((atoms x).numerical hr) ((atoms y).numerical hr) +
        productSum lbits rbits x y + productSum lbits rbits y x

end Lax342547.AtomProducts
