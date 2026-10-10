import Lax342547.GradientRealization
import Lax342547.RawContractions

/-!
---
title: Actual gradient agreement and matched keys produce all four cross holes
type: definition and theorem
---
The paired witnesses supply tensor sharing and role parity. Whole-space gradient agreement of actual cross contractions then gives both hole equations for each of the four cross pairs, with the original left and right witness lists.
-/

namespace Lax342547.FourHoles

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.TableContractions Lax342547.RawContractions Lax342547.RawFrames
open Lax342547.HoleRelation

axiom four_holes {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (holes : HoleData (Component (Tag k) → Frame (Coordinate k n b degree) H N E)
      (Profile k n b degree) (Component (Tag k) → Matrix N N Binary))
    (hrole : holes.a = D.role) (hgradient : holes.T = gradient D L R)
    (hU : ∀ o, holes.U o = (profileMap o).comp (Profile k n b degree).subtype)
    (hu : ∀ o, holes.u o = profileContraction o)
    (hkeys : MatchedKeys W oA oB)
    (hroles : ∀ i z, D.role (leftWitness W i z) + D.role (rightWitness W i z) = 1)
    (hleft : ∀ i z x, fullContraction (rawForms oA oB) (Profile k n b degree) i z x =
      (D.role + gradient D L R (leftWitness W i z)) x)
    (hright : ∀ i z x, fullContraction (rawForms oA oB).flip (Profile k n b degree) z i x =
      (D.role + gradient D L R (rightWitness W i z)) x) :
    ∀ i z, Hole holes (oA i) (oB z)

end Lax342547.FourHoles
