import Lax342547.FourHoles

/-!
---
title: Finite primal-channel records with the paper bit count and four-hole implication
type: definition and theorem
---
Recording both modes and reciprocal roles takes exactly 16|E|h dimB bits. Equality of these records fixes every actual primal-to-channel evaluation and hence every contraction. Matched keys, witness parity and the constructed gradients then force all four actual cross pairs to be holes.
-/

namespace Lax342547.PrimalRecords

open Lax342547.MomentSpace Lax342547.TableContractions Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.TagGeometry Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.RawContractions Lax342547.RawFrames Lax342547.HoleRelation

abbrev EntryIndex (Comp B H : Type) := Fin 2 × Fin 2 × Comp × Fin 2 × Fin 2 × B × H

noncomputable def entries {Comp B H : Type} [Fintype H] (F : CrossForms Comp B H) :
    EntryIndex Comp B H → Binary := by
  classical
  exact fun t =>
    let G := if t.1 = 0 then F else F.flip
    let m := if t.2.1 = 0 then fullPlus G t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
      else fullMinus G t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
    m (Pi.single t.2.2.2.2.2.1 1) t.2.2.2.2.2.2

axiom entry_count {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H] :
    Fintype.card (EntryIndex Comp B H) = 16 * Fintype.card Comp * Fintype.card H * Fintype.card B

def Agreement {Comp B H : Type} [Fintype H] (F G : CrossForms Comp B H) : Prop :=
  (∀ e i z, fullPlus F e i z = fullPlus G e i z ∧ fullMinus F e i z = fullMinus G e i z) ∧
  (∀ e i z, fullPlus F.flip e i z = fullPlus G.flip e i z ∧ fullMinus F.flip e i z = fullMinus G.flip e i z)

axiom coordinate_map_ext {B H : Type} [Fintype B] [Fintype H]
    (f g : (B → Binary) →ₗ[Binary] (H → Binary)) : by
      classical
      exact (∀ b h, f (Pi.single b 1) h = g (Pi.single b 1) h) → f = g

axiom entries_determine {Comp B H : Type} [Fintype B] [Fintype H]
    (F G : CrossForms Comp B H) (heq : entries F = entries G) : Agreement F G

axiom agreement_contractions {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (F G : CrossForms Comp B H) (h : Agreement F G)
    (X : Submodule Binary (Comp → Matrix B B Binary)) :
    (∀ i z, fullContraction F X i z = fullContraction G X i z) ∧
    (∀ i z, fullContraction F.flip X i z = fullContraction G.flip X i z)

axiom entries_give_four_holes {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
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
    (G : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (heq : entries (rawForms oA oB) = entries G)
    (hleft : ∀ i z x, fullContraction G (Profile k n b degree) i z x =
      (D.role + gradient D L R (leftWitness W i z)) x)
    (hright : ∀ i z x, fullContraction G.flip (Profile k n b degree) z i x =
      (D.role + gradient D L R (rightWitness W i z)) x) :
    ∀ i z, Hole holes (oA i) (oB z)

axiom record_count {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H] :
    by
      classical
      exact Fintype.card (EntryIndex Comp B H → Binary) =
        2 ^ (16 * Fintype.card Comp * Fintype.card H * Fintype.card B)

end Lax342547.PrimalRecords
