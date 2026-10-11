import Lax342547.RawBaselines

/-!
---
title: Baseline contractions on the selected atoms
type: lemma
---
Freezing both signs of an atom's key retains its actual contraction.
Matched keys then give zero toward the atom's matched endpoint and the
opposite own-unit contraction toward the other endpoint. These are the
values prescribed by the binary recipe.
-/

namespace Lax342547.FrozenValues

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.TableContractions Lax342547.RawContractions Lax342547.RawBaselines

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}
  {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

axiom frozen_atom (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (hfrozen : Frozen F W P Q oA oB) (i z z' : Fin 2) (t : Fin (W.length i z')) :
    fullContraction F (Profile k n b degree) i z (W.left i z' t).profile =
      fullContraction (rawForms oA oB) (Profile k n b degree) i z (W.left i z' t).profile

axiom selected_values (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (oA oB : Unit (H := H) (N := N) (E := E))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H)
    (hfrozen : Frozen F W P Q oA oB) (hkeys : MatchedKeys W oA oB)
    (i z z' : Fin 2) (t : Fin (W.length i z')) :
    fullContraction F (Profile k n b degree) i z (W.left i z' t).profile =
      if z = z' then 0 else ownContraction oB z' (W.right i z' t).profile

end Lax342547.FrozenValues
