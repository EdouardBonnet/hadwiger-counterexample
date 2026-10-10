import Lax342547.PrimalRecords
import Lax342547Proofs.FourHoles

namespace Lax342547Proofs.PrimalRecords
open Lax342547.PrimalRecords

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.TableContractions Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.TagGeometry Lax342547.CutProfiles

/--
---
conclusion: Lax342547.PrimalRecords.entry_count
---
-/
theorem entry_count {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H] :
    Fintype.card (EntryIndex Comp B H) = 16 * Fintype.card Comp * Fintype.card H * Fintype.card B := by
  simp only [EntryIndex, Fintype.card_prod, Fintype.card_fin]
  ring

/--
---
conclusion: Lax342547.PrimalRecords.coordinate_map_ext
---
-/
theorem coordinate_map_ext {B H : Type} [Fintype B] [Fintype H]
    (f g : (B → Binary) →ₗ[Binary] (H → Binary)) : by
      classical
      exact (∀ b h, f (Pi.single b 1) h = g (Pi.single b 1) h) → f = g := by
  classical
  intro hfg
  apply LinearMap.toMatrix'.injective
  ext h b
  exact hfg b h

/--
---
conclusion: Lax342547.PrimalRecords.entries_determine
---
-/
theorem entries_determine {Comp B H : Type} [Fintype B] [Fintype H]
    (F G : CrossForms Comp B H) (heq : entries F = entries G) : Agreement F G := by
  classical
  have hentry (role mode : Fin 2) (e : Comp) (i z : Fin 2) (b : B) (h : H) :=
    congrFun heq (role, mode, e, i, z, b, h)
  constructor
  · intro e i z
    constructor
    · apply coordinate_map_ext
      intro b h
      exact hentry 0 0 e i z b h
    · apply coordinate_map_ext
      intro b h
      exact hentry 0 1 e i z b h
  · intro e i z
    constructor
    · apply coordinate_map_ext
      intro b h
      exact hentry 1 0 e i z b h
    · apply coordinate_map_ext
      intro b h
      exact hentry 1 1 e i z b h

/--
---
conclusion: Lax342547.PrimalRecords.agreement_contractions
---
-/
theorem agreement_contractions {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (F G : CrossForms Comp B H) (h : Agreement F G)
    (X : Submodule Binary (Comp → Matrix B B Binary)) :
    (∀ i z, fullContraction F X i z = fullContraction G X i z) ∧
    (∀ i z, fullContraction F.flip X i z = fullContraction G.flip X i z) := by
  constructor
  · intro i z
    simp only [fullContraction, (h.1 _ i z).1, (h.1 _ i z).2]
  · intro i z
    simp only [fullContraction, (h.2 _ i z).1, (h.2 _ i z).2]


open Lax342547.PairedWitnesses Lax342547.RawContractions Lax342547.RawFrames Lax342547.HoleRelation

/--
---
conclusion: Lax342547.PrimalRecords.entries_give_four_holes
---
-/
theorem entries_give_four_holes {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
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
    ∀ i z, Hole holes (oA i) (oB z) := by
  have hc := agreement_contractions (rawForms oA oB) G
    (entries_determine (rawForms oA oB) G heq) (Profile k n b degree)
  apply Lax342547Proofs.FourHoles.four_holes W D L R oA oB holes hrole hgradient hU hu hkeys hroles
  · intro i z x
    rw [hc.1 i z]
    exact hleft i z x
  · intro i z x
    rw [hc.2 z i]
    exact hright i z x


/--
---
conclusion: Lax342547.PrimalRecords.record_count
---
-/
theorem record_count {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H] :
    by
      classical
      exact Fintype.card (EntryIndex Comp B H → Binary) =
        2 ^ (16 * Fintype.card Comp * Fintype.card H * Fintype.card B) := by
  classical
  rw [Fintype.card_fun, ZMod.card, entry_count]

end Lax342547Proofs.PrimalRecords
