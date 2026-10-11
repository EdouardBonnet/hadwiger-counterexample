import Lax342547.CommonAtoms
import Lax342547.PointQuadratics
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
---
title: Actual point atoms determine cut-space functionals
type: lemma
---
Ambient extension realizes every atom evaluation as a local tensor functional, with actual base degree two and point-atom extensionality on the whole concrete cut space.
-/

namespace Lax342547.AtomFunctionals

open Lax342547.MomentSpace Lax342547.Atoms Lax342547.TagGeometry Lax342547.ConcreteCut
open Lax342547.ConcreteGeometry Lax342547.CutProfiles Lax342547.SelectorInterpolation
open scoped BigOperators

noncomputable def starMatrixMap {k n b degree : ℕ} (l : Tag k) :
    Moment k n b degree →ₗ[Binary] (Component (Tag k) → Moment k n b degree) := by
  classical
  exact { toFun := fun M e => if l ∈ e.val then M else 0
          map_add' := by intro x y; funext e; by_cases h : l ∈ e.val <;> simp [h]
          map_smul' := by intro c x; funext e; by_cases h : l ∈ e.val <;> simp [h] }

axiom atom_local_functional {k n b degree : ℕ} (l : Tag k)
    (φ : Module.Dual Binary (Profile k n b degree)) :
    ∃ ψ : Module.Dual Binary (Moment k n b degree),∀ s z
      (hz : ∀ i,i ∉ allowedBase k n l → z i = 0),
      φ (atom (degree := degree) l s z hz) = ψ (pointMoment selectorEval s z)

axiom cut_star_sum {k n b degree : ℕ} (w : Tag k → Moment k n b degree) :
    cutMap w = ∑ l,starMatrixMap l (w l)

axiom atom_functional_ext {k n b degree : ℕ} (φ : Module.Dual Binary (Profile k n b degree))
    (hφ : ∀ l s z (hz : ∀ i,i ∉ allowedBase k n l → z i = 0),
      φ (atom (degree := degree) l s z hz) = 0) : φ = 0

axiom atom_base_degree {k n b degree r : ℕ} (l : Tag k) (s : Fin b → Binary)
    (φ : Module.Dual Binary (Profile k n b degree))
    (z : (Fin r → Binary) → Base k n → Binary)
    (hz : ∀ x i,i ∉ allowedBase k n l → z x i = 0)
    (hdegree : ∀ i,(fun x => z x i) ∈ selectorSpan r 1) :
    (fun x => φ (atom (degree := degree) l s (z x) (hz x))) ∈ selectorSpan r 2

end Lax342547.AtomFunctionals
