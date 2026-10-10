import Lax342547.FourHoles
import Lax342547Proofs.GradientRealization
import Lax342547Proofs.RawContractions

namespace Lax342547Proofs.FourHoles
open Lax342547.FourHoles

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.TableContractions Lax342547.RawContractions Lax342547.RawFrames
open Lax342547.HoleRelation

/--
---
conclusion: Lax342547.FourHoles.four_holes
---
-/
theorem four_holes {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
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
    ∀ i z, Hole holes (oA i) (oB z) := by
  intro i z
  refine ⟨leftWitness W i z, rightWitness W i z, ?_, ?_, ?_, ?_⟩
  · rw [hU, hU]
    exact Lax342547Proofs.PairedWitnesses.tensor_sharing W oA oB hkeys i z
  · intro x
    rw [hu, hU, hrole, hgradient]
    change profileContraction (oB z) (profileMap (oA i) x.val) = _
    rw [← Lax342547Proofs.RawContractions.raw_contraction oA oB]
    exact hleft i z x
  · intro x
    rw [hu, hU, hrole, hgradient]
    change profileContraction (oA i) (profileMap (oB z) x.val) = _
    rw [← Lax342547Proofs.RawContractions.raw_contraction oB oA]
    exact hright i z x
  · rw [hrole]
    exact hroles i z

end Lax342547Proofs.FourHoles
