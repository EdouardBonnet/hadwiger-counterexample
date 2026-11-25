import Lax793645Proofs.Simplifications.OneQueryCellRecentring
import Lax793645Proofs.Simplifications.OneCommonPredictions
import Lax793645Proofs.Simplifications.PolynomialSubstitution
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PointAtomVanishing

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Function Submodule Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N : ℕ}

def flattenKnobs (p : Shape) (n : ℕ) : Base p.g n≃ₗ[F]Knobs p.g n where
  toFun := curry
  invFun := uncurry
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem flatten_knobs_uniform :
    mapW unif (flattenKnobs p n)=spins p n := by
  rw [spins,←draws_unif]
  exact unif_equiv (flattenKnobs p n).toEquiv

def flatSpring (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) :
    Base p.g n→ₗ[F]Ray p n := (springLinear p l s f).comp (flattenKnobs p n).toLinearMap

theorem flat_spring_affine (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (z : Base p.g n) : spring p l s f (flattenKnobs p n z)=
      flatSpring l s f z+spring p l s f 0 := by
  simp only [flatSpring,LinearMap.comp_apply,LinearEquiv.coe_coe,
    springLinear,LinearMap.coe_mk,AddHom.coe_mk,sub_add_cancel]

/-- Every linear functional on the profile space is quadratic in the
ordinary point parameters, at a fixed selector label. -/
theorem one_input_functional_quadratic (w : Pdual p n) (l : Tag p.g)
    (s : Label p.b) (f : Flavor p.g) :
    (fun z : Base p.g n=>w (useAtom p l s f (flattenKnobs p n z)))∈Stocks (BaseIdx p.g n) 2 := by
  let L := w.comp ((cut p n).comp (LinearMap.single F (fun _ : Tag p.g=>Moment p n) l))
  have hh := pointPoly L (fun z=>spring p l s f (flattenKnobs p n z)) 1
    (fun i=>by
      simp_rw [flat_spring_affine]
      exact affine_coordinate_stocks (flatSpring l s f) (spring p l s f 0) i)
  exact hh

theorem one_input_tester_quadratic (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) :
    (fun z : Base p.g n=>dialed p l f (flattenKnobs p n z))∈Stocks (BaseIdx p.g n) 2 := by
  have hh := pointPoly (eta p n) (fun z=>spring p l s f (flattenKnobs p n z)) 1
    (fun i=>by
      simp_rw [flat_spring_affine]
      exact affine_coordinate_stocks (flatSpring l s f) (spring p l s f 0) i)
  convert hh using 1
  funext z
  exact etaScan p l s f _

def flatFree (p : Shape) (n : ℕ) : Vec (Fin n)→ₗ[F]Base p.g n :=
  (flattenKnobs p n).symm.toLinearMap.comp (freeKnob p n)

theorem dialed_add_free (l : Tag p.g) (f : Flavor p.g) (x : Knobs p.g n)
    (z : Vec (Fin n)) : dialed p l f (x+freeKnob p n z)=dialed p l f x := by
  classical
  have he : x+freeKnob p n z=update x Block.Z (x Block.Z+z) := by
    funext B
    by_cases hB : B=Block.Z <;> simp [freeKnob,hB]
  rw [he]
  unfold dialed
  rw [scannedZ]

theorem flat_tester_free (l : Tag p.g) (f : Flavor p.g) (x : Base p.g n)
    (z : Vec (Fin n)) :
    dialed p l f (flattenKnobs p n (x+flatFree p n z))=
      dialed p l f (flattenKnobs p n x) := by
  rw [map_add]
  exact dialed_add_free l f _ z

end
end Lax793645Proofs.Simplifications
