import Lax342547.AtomFunctionals
import Lax342547.PolynomialTensors

/-!
---
title: Actual finite atom parameterization and degrees
type: lemma
---
Every flavor is parameterized by its retained binary coordinates; generic parameters cover all allowed base points, and actual atom/base/selector degrees are checked.
-/

namespace Lax342547.AtomParameters

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut
open Lax342547.ConcreteGeometry Lax342547.SelectorInterpolation

noncomputable def ParameterSize {k : ℕ} (n : ℕ) (l : Tag k) (f : Flavor k) :=
  Fintype.card {i : Base k n // i ∈ retained l f}

noncomputable def parameterBase {k n : ℕ} (l : Tag k) (f : Flavor k)
    (x : Fin (ParameterSize n l f) → Binary) (i : Base k n) : Binary := by
  classical
  exact if hi : i ∈ retained l f then x ((Fintype.equivFin _).toFun ⟨i,hi⟩) else 0

noncomputable def parameterAtom {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (f : Flavor k)
    (x : Fin (ParameterSize n l f) → Binary) : Profile k n b degree :=
  atom l s (parameterBase l f x) (by
    classical
    intro i hi
    have hn : i ∉ retained l f := by
      rintro hf
      apply hi
      cases i with
      | inl j => exact hf.1
      | inr j => trivial
    simp [parameterBase,hn])

axiom parameter_coordinate_degree {k n : ℕ} (l : Tag k) (f : Flavor k) (i : Base k n) :
    (fun x => parameterBase l f x i) ∈ selectorSpan (ParameterSize n l f) 1

axiom generic_parameters_cover {k n : ℕ} (l : Tag k) (z : Base k n → Binary)
    (hz : ∀ i,i ∉ allowedBase k n l → z i = 0) :
    ∃ x : Fin (ParameterSize n l Flavor.generic) → Binary,parameterBase l Flavor.generic x = z

axiom parameter_atom_degree {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (f : Flavor k)
    (φ : Module.Dual Binary (Profile k n b degree)) :
    (fun x => φ (parameterAtom (degree := degree) l s f x)) ∈ selectorSpan (ParameterSize n l f) 2

axiom atom_selector_degree {k n b degree : ℕ} (l : Tag k) (φ : Module.Dual Binary (Profile k n b degree))
    (z : Base k n → Binary) (hz : ∀ i,i ∉ allowedBase k n l → z i = 0) :
    (fun s => φ (atom (degree := degree) l s z hz)) ∈ selectorSpan b (degree+degree)

axiom parameter_tensor_degree {k n b degree : ℕ} (l : Tag k) (s : Fin b → Binary) (f : Flavor k)
    (ψ : Module.Dual Binary (Moment k n b degree)) :
    (fun x => ψ (pointMoment selectorEval s (parameterBase l f x))) ∈ selectorSpan (ParameterSize n l f) 2

end Lax342547.AtomParameters
