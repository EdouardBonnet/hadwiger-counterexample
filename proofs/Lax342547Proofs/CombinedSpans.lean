import Lax342547.CombinedSpans
import Mathlib.LinearAlgebra.Prod
import Lax342547.GreedySpans

namespace Lax342547Proofs.CombinedSpans
open Lax342547.CombinedSpans

set_option backward.isDefEq.respectTransparency false
open Lax342547.GreedySpans Lax342547.GreedyTails
open scoped BigOperators

/--
---
conclusion: Lax342547.CombinedSpans.product_space_dimension
---
-/
theorem product_space_dimension {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (C : Submodule K V) (R : Submodule K W) :
    Module.finrank K (C.prod R) = Module.finrank K C+Module.finrank K R := by
  rw [(productSpaceEquiv C R).finrank_eq,Module.finrank_prod]

/--
---
conclusion: Lax342547.CombinedSpans.gain_product
---
-/
theorem gain_product {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (U C : Submodule K V) (Z R : Submodule K W) :
    gain (U.prod Z) (C.prod R) = gain U C+gain Z R := by
  unfold gain
  rw [Submodule.prod_sup_prod,Lax342547.CombinedSpans.product_space_dimension,Lax342547.CombinedSpans.product_space_dimension]
  push_cast
  ring

/--
---
conclusion: Lax342547.CombinedSpans.span_after_product
---
-/
theorem span_after_product {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (C : ι → Submodule K V) (R : ι → Submodule K W)
    (U : Submodule K V) (Z : Submodule K W) (l : List ι) :
    spanAfter (fun i => (C i).prod (R i)) (U.prod Z) l =
      (spanAfter C U l).prod (spanAfter R Z l) := by
  induction l generalizing U Z with
  | nil => rfl
  | cons i l ih => simpa only [spanAfter,Submodule.prod_sup_prod] using ih (U ⊔ C i) (Z ⊔ R i)

/--
---
conclusion: Lax342547.CombinedSpans.sum_gain_product
---
-/
theorem sum_gain_product {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (C : ι → Submodule K V) (R : ι → Submodule K W)
    (U : Submodule K V) (Z : Submodule K W) (l : List ι) :
    (l.map (fun i => gain (U.prod Z) ((C i).prod (R i)))).sum =
      (l.map (fun i => gain U (C i))).sum+(l.map (fun i => gain Z (R i))).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [Lax342547.CombinedSpans.gain_product,ih]
    ring

/--
---
conclusion: Lax342547.CombinedSpans.deficit_product
---
-/
theorem deficit_product {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (C : ι → Submodule K V) (R : ι → Submodule K W)
    (U : Submodule K V) (Z : Submodule K W) (l : List ι) :
    deficit (fun i => (C i).prod (R i)) (U.prod Z) l = deficit C U l+deficit R Z l := by
  unfold deficit
  rw [Lax342547.CombinedSpans.sum_gain_product]
  simp only [Lax342547.GreedySpans.increments_sum]
  rw [Lax342547.CombinedSpans.span_after_product,Lax342547.CombinedSpans.product_space_dimension,Lax342547.CombinedSpans.product_space_dimension]
  push_cast
  ring

end Lax342547Proofs.CombinedSpans
