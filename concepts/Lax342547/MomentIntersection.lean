import Lax342547.MomentSpace

/-!
---
title: Intersections of restricted moment spaces
type: lemma
---
Intersecting coordinate restrictions commutes with taking the span of
Boolean point moments. This supplies the coordinate-projection step in
Lemma 2.3, including infinite nonempty families of restrictions.
-/

namespace Lax342547.MomentIntersection

open Lax342547.MomentSpace

axiom momentSpace_iInter {Label Coord Base : Type}
    (p : Label → Coord → Binary) {Tag : Type} [Nonempty Tag] (A : Tag → Set Base) :
    momentSpace p (⋂ t, A t) = ⨅ t, momentSpace p (A t)

end Lax342547.MomentIntersection
