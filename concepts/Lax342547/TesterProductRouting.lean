import Lax342547.FixedSelectorGram

/-!
---
title: Prescribed Gram products routed into distinct retained tester pairs
type: definition and theorem
---
Each prescribed Gram product is routed to a distinct retained tester
pair. The exact uniform tester restriction law then supplies a positive
real conditioning mass without restricting the growing free coefficients.
-/

namespace Lax342547.TesterProductRouting
noncomputable section
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.Atoms
open Lax342547.FixedSelectorGram Lax342547.FlavorAffineSlices Lax342547.AffineSliceIndependence
open Lax342547.ConcreteGeometry Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false


def productRouting {k r : ℕ} {l : Tag k} {f : Flavor k} {D I : Type}
    (c : I → Pairs l f r) (a b : I → Option D → Binary) :
    Matrix (Slots l f r) (Option D) Binary := by
  classical
  exact fun u j => if u.2.2 then Function.extend c (fun i => b i j) 0 (u.1,u.2.1)
    else Function.extend c (fun i => a i j) 0 (u.1,u.2.1)

axiom sum_extended_product {I J : Type} [Fintype I] [Fintype J]
    (c : I → J) (hc : Function.Injective c) (a b : I → Binary) :
    (∑ j,Function.extend c a 0 j*Function.extend c b 0 j) = ∑ i,a i*b i

axiom routed_product_gram {k r : ℕ} {l : Tag k} {f : Flavor k} {D I : Type}
    [Fintype I] (c : I → Pairs l f r) (hc : Function.Injective c)
    (a b : I → Option D → Binary) :
    restrictedGram (productRouting c a b) = fun x y => ∑ i,a i x*b i y

axiom product_gram_cell_mass {k n b degree r : ℕ} {D I : Type} [Fintype D] [Fintype I]
    (hr : 2*r ≤ n) (hd : 1 ≤ degree)
    (M : Fin b → Matrix (Fin n) (Fin n) Binary) (s : Fin b → Binary)
    (l : Tag k) (f : Flavor k) (c : I → Pairs l f r) (hc : Function.Injective c)
    (a b' : I → Option D → Binary) :
    massFloor l f r D ≤ cellMass
      (weights (PMF.uniformOfFintype (Coefficients n l f D)))
      (fun V => (pointColumns s (value V)).transpose*selfGram hr hd M*pointColumns s (value V) =
        fun x y => ∑ i,a i x*b' i y)

end
end Lax342547.TesterProductRouting
