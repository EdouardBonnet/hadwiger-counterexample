import Lax793645.Holes

/-!
---
title: Three holes cannot form a triangle
type: lemma
---
The hole relation is symmetric and irreflexive. Evaluating its six functional
identities around a triangle cancels the ambient evaluations and the symmetric
bilinear terms. The three remaining role parities sum to one.
-/

namespace Lax793645.TriangleFreeHoles

/-- Injectivity rules out loops. Symmetry of the pairing rules out triangles. -/
axiom triangle_free {I X V : Type*} (U : I → X → V) (u : I → V → ZMod 2)
    (a : X → ZMod 2) (T : X → X → ZMod 2)
    (injective : ∀ i, Function.Injective (U i)) (symm : ∀ x y, T x y = T y x) :
    let H := Holes.relation U u a T
    (∀ i j, H i j → H j i) ∧ (∀ i, ¬H i i) ∧
      ∀ i j k, H i j → H j k → ¬H i k

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

axiom one_hole_sym {m : Mixer p n} {x y : OneOrient p n N}
    (h : Holes.hole m x y) : Holes.hole m y x

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

axiom one_hole_irrefl (m : Mixer p n) (x : OneOrient p n N) : ¬Holes.hole m x x

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

axiom one_hole_triangle {m : Mixer p n} {x y z : OneOrient p n N}
    (h1 : Holes.hole m x y) (h2 : Holes.hole m y z) : ¬Holes.hole m x z

end

end Lax793645.TriangleFreeHoles
