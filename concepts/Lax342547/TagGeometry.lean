import Lax342547.CutProfiles
import Mathlib.Data.ZMod.Basic

/-!
---
title: Majority intersections in the cyclic tag geometry
type: lemma
---
For $g=2k+1$, the tag $l$ allows the block $O_{d,t}$ exactly when
$l\in\{d+1,\ldots,d+k\}$. The other three blocks are unrestricted.
The intersection over more than $k$ tags is the all-$O$-zero moment
space, as asserted in the first part of Lemma 2.3.
-/

namespace Lax342547.TagGeometry

open Lax342547.MomentSpace

abbrev Tag (k : ℕ) := ZMod (2 * k + 1)

def interval (k : ℕ) (d : Tag k) : Finset (Tag k) :=
  Finset.univ.image (fun i : Fin k => d + (i.val + 1 : ℕ))

abbrev Base (k n : ℕ) := ((Tag k × Tag k) × Fin n) ⊕ (Fin 3 × Fin n)

def allowedBase (k n : ℕ) (l : Tag k) : Set (Base k n)
  | Sum.inl ((d, _), _) => l ∈ interval k d
  | Sum.inr _ => True

def commonBase (k n : ℕ) : Set (Base k n)
  | Sum.inl _ => False
  | Sum.inr _ => True

axiom majority_intersection {Label Coord : Type} (k n : ℕ)
    (p : Label → Coord → Binary) (S : Finset (Tag k)) (hS : k < S.card) :
    (⨅ l : {l // l ∈ S}, momentSpace p (allowedBase k n l.val)) =
      momentSpace p (commonBase k n)

end Lax342547.TagGeometry
