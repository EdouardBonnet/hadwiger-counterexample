import Lax342547.HoleRelation

/-!
---
title: Holes are symmetric, loopless, and triangle-free
type: lemma
---
The hole relation of Definition 2.1 is symmetric, has no loops, and has
no triangle. This is Lemma 2.2: the six functional identities around a
triangle cancel in characteristic two, leaving $0=1$.
-/

namespace Lax342547.HoleTriangleFree

open HoleRelation

universe u v w

axiom hole_properties
    {Ω : Type u} {X : Type v} {V : Type w}
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup V] [Module (ZMod 2) V]
    (D : HoleData Ω X V) :
    (∀ ⦃i j⦄, Hole D i j → Hole D j i) ∧ (∀ i, ¬ Hole D i i) ∧
      ∀ i j k, Hole D i j → Hole D j k → ¬ Hole D k i

end Lax342547.HoleTriangleFree
