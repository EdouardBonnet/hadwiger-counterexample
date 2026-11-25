import Lax793645.ConstructionData

/-!
---
title: Prescribing pairings on a witness list
type: lemma
---
The scalar balance equations allow binary prescriptions for the selected atoms. These
prescriptions fix the required gradient on each selected direction and the scalar
recipe fixes it on the effective profiles.
-/

namespace Lax793645.ScalarPrescriptions

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {I : Type}
variable [Fintype I]

axiom choose_reduced_script (p : Shape) (t : Tagging p I) (a b : I→ Bool)
    (d f d' : Vec I)
    (h : ∀ i : Bool,(∑ x∈aiming a b i true,(d' x+f x))=
      ∑ x∈aiming a b i false,(d' x+f x))
    (ha : ∀ i j : Bool,∑ x∈aiming a b i j,(d x+d' x)=1)
    (hc : ∀ i j : Bool,(aiming a b i j).Nonempty)
    (u : Mat I I) (hu : uᵀ=u) (hg : 3≤ p.g) (hodd : Odd p.g) (hJ : 1≤ p.J) :
    ∃ s : Script p I,fulfills p t d f u (reducedScript s) a b

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
variable {I : Type} [Fintype I]

axiom one_recipe_atoms (v w : Volley p n I) (t : Tagging p I) (m : Mixer p n)
    (x y : OneUnit p n N) (hv : v.legal t) (hy : ∀ i,oneFrameLaw m (y i))
    (hkeys : oneVolleyKeys v t x=oneVolleyKeys w t y) (hat : oneAttackGrad v w t m y)
    (M : Bool→ JointProfile p n)
    (hgrad : ∀ i j z,jointMatrixFunctional (M j) (jointEndpointMap i z)=grad m (v.sumAt t w.obj i j) z)
    (j : Bool) (a : I) :
    jointMatrixFunctional (M j) (jointEndpointMap (v.obj a) (v.atomAt t a))=
      jointMatrixFunctional
        (fun e=> channelQuadraticMatrix p.h (unitLeftChannels p.h (oneUnitActual x y e) j))
        (jointEndpointMap (v.obj a) (v.atomAt t a))

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}
variable {I : Type} [Fintype I]

axiom one_recipe_effective (v : Volley p n I) (w : I→ Bool) (t : Tagging p I)
    (m : Mixer p n) (x y : OneUnit p n N) (P : Bool→ Comp p.g→ Space (Ray p n))
    (hrecipe : OneScalarRecipe v w t m x y P) (M : Bool→ JointProfile p n)
    (hgrad : ∀ i j z,jointMatrixFunctional (M j) (jointEndpointMap i z)=grad m (v.sumAt t w i j) z)
    (j : Bool) (z : JointProfile p n) (hz : z∈jointXspace)
    (hp : ∀ e,z e∈quadraticSquares (jointSpace (fun i=> P i e))) :
    jointMatrixFunctional (M j) z=jointMatrixFunctional
      (fun e=> channelQuadraticMatrix p.h (unitLeftChannels p.h (oneUnitActual x y e) j)) z

end

end Lax793645.ScalarPrescriptions
