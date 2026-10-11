import Lax342547.ActualDeficits
import Mathlib.LinearAlgebra.Prod

/-!
---
title: Combined column and row mode exposure
type: definition and theorem
---
Products of the two mode spaces have additive dimensions, gains, and deficits, allowing one greedy exposed set to control both modes.
-/

namespace Lax342547.CombinedSpans

open Lax342547.GreedySpans Lax342547.GreedyTails
open scoped BigOperators

noncomputable def productSpaceEquiv {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (C : Submodule K V) (R : Submodule K W) :
    (C.prod R) ≃ₗ[K] C × R :=
  { toFun := fun v => (⟨v.val.1,v.property.1⟩,⟨v.val.2,v.property.2⟩)
    invFun := fun v => ⟨(v.1.val,v.2.val),v.1.property,v.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

axiom product_space_dimension {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (C : Submodule K V) (R : Submodule K W) :
    Module.finrank K (C.prod R) = Module.finrank K C+Module.finrank K R

axiom gain_product {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (U C : Submodule K V) (Z R : Submodule K W) :
    gain (U.prod Z) (C.prod R) = gain U C+gain Z R

axiom span_after_product {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (C : ι → Submodule K V) (R : ι → Submodule K W)
    (U : Submodule K V) (Z : Submodule K W) (l : List ι) :
    spanAfter (fun i => (C i).prod (R i)) (U.prod Z) l =
      (spanAfter C U l).prod (spanAfter R Z l)

axiom sum_gain_product {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (C : ι → Submodule K V) (R : ι → Submodule K W)
    (U : Submodule K V) (Z : Submodule K W) (l : List ι) :
    (l.map (fun i => gain (U.prod Z) ((C i).prod (R i)))).sum =
      (l.map (fun i => gain U (C i))).sum+(l.map (fun i => gain Z (R i))).sum

axiom deficit_product {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (C : ι → Submodule K V) (R : ι → Submodule K W)
    (U : Submodule K V) (Z : Submodule K W) (l : List ι) :
    deficit (fun i => (C i).prod (R i)) (U.prod Z) l = deficit C U l+deficit R Z l

end Lax342547.CombinedSpans
