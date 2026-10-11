import Lax342547.AtomParameters
import Lax342547.AtomFunctionals
import Lax342547.PolynomialTensors
import Lax342547.QuadraticDegree
import Lax342547Proofs.SelectorInterpolation

namespace Lax342547Proofs.AtomParameters
open Lax342547.AtomParameters

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut
open Lax342547.ConcreteGeometry Lax342547.SelectorInterpolation

/--
---
conclusion: Lax342547.AtomParameters.parameter_coordinate_degree
---
-/
theorem parameter_coordinate_degree {k n : ℕ} (l : Tag k) (f : Flavor k) (i : Base k n) :
    (fun x => parameterBase l f x i) ∈ selectorSpan (ParameterSize n l f) 1 := by
  classical
  by_cases hi : i ∈ retained l f
  · have hh := Lax342547Proofs.SelectorInterpolation.affine_mem
      ((Fintype.equivFin {i : Base k n // i ∈ retained l f}).toFun ⟨i,hi⟩) 0
    simpa [parameterBase,hi,ParameterSize] using hh
  · simpa [parameterBase,hi] using
      Lax342547Proofs.SelectorInterpolation.constant_mem (b := ParameterSize n l f) 0 1

/--
---
conclusion: Lax342547.AtomParameters.generic_parameters_cover
---
-/
theorem generic_parameters_cover {k n : ℕ} (l : Tag k) (z : Base k n → Binary)
    (hz : ∀ i,i ∉ allowedBase k n l → z i = 0) :
    ∃ x : Fin (ParameterSize n l Flavor.generic) → Binary,parameterBase l Flavor.generic x = z := by
  classical
  let e := Fintype.equivFin {i : Base k n // i ∈ retained l Flavor.generic}
  refine ⟨fun j => z (e.symm j).val,?_⟩
  ext i
  by_cases hi : i ∈ retained l Flavor.generic
  · simp [parameterBase,hi,e]
  · have hn : i ∉ allowedBase k n l := by
      intro ha
      apply hi
      cases i with
      | inl j => exact ⟨ha,trivial⟩
      | inr j => trivial
    simp [parameterBase,hi,hz i hn]

/--
---
conclusion: Lax342547.AtomParameters.parameter_atom_degree
---
-/
theorem parameter_atom_degree {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (f : Flavor k)
    (φ : Module.Dual Binary (Profile k n b degree)) :
    (fun x => φ (parameterAtom (degree := degree) l s f x)) ∈ selectorSpan (ParameterSize n l f) 2 := by
  unfold parameterAtom
  apply Lax342547.AtomFunctionals.atom_base_degree
  exact Lax342547.AtomParameters.parameter_coordinate_degree l f

/--
---
conclusion: Lax342547.AtomParameters.atom_selector_degree
---
-/
theorem atom_selector_degree {k n b degree : ℕ} (l : Tag k) (φ : Module.Dual Binary (Profile k n b degree))
    (z : Base k n → Binary) (hz : ∀ i,i ∉ allowedBase k n l → z i = 0) :
    (fun s => φ (atom (degree := degree) l s z hz)) ∈ selectorSpan b (degree+degree) := by
  obtain ⟨ψ,hψ⟩ := Lax342547.AtomFunctionals.atom_local_functional l φ
  have he : (fun s => φ (atom (degree := degree) l s z hz)) =
      (fun s => ψ (pointMoment selectorEval s z)) := funext (fun s => hψ s z hz)
  rw [he]
  exact Lax342547.PolynomialTensors.selector_tensor_degree ψ z

/--
---
conclusion: Lax342547.AtomParameters.parameter_tensor_degree
---
-/
theorem parameter_tensor_degree {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (f : Flavor k)
    (ψ : Module.Dual Binary (Moment k n b degree)) :
    (fun x => ψ (pointMoment selectorEval s (parameterBase l f x))) ∈ selectorSpan (ParameterSize n l f) 2 := by
  have hf (i : SelectorCoordinates b degree × Option (Base k n)) :
      (fun x => point selectorEval s (parameterBase l f x) i) ∈ selectorSpan (ParameterSize n l f) 1 := by
    apply (selectorSpan (ParameterSize n l f) 1).smul_mem (selectorEval s i.1)
    cases i.2 with
    | none => exact Lax342547Proofs.SelectorInterpolation.constant_mem 1 1
    | some j => exact Lax342547.AtomParameters.parameter_coordinate_degree l f j
  exact Lax342547.QuadraticDegree.linear_outer_product_degree ψ
    (fun i x => point selectorEval s (parameterBase l f x) i) hf

end Lax342547Proofs.AtomParameters
