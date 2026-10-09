import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
---
title: Finite linear images and their uniform-law density bounds
type: theorem
---
Surjective linear observation cannot increase the codimension of a
subspace. Over the binary field, an image of codimension at most c has
point masses bounded by 2^c times the full-space uniform point mass.
These are the projection and domination steps used for mixer row bits.
-/

namespace Lax342547.FiniteLinearLaw

def familyMap {K T : Type} [Field K] {V W : T → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) : (∀ i, V i) →ₗ[K] (∀ i, W i) :=
  LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))

axiom family_codimension {K T : Type} [Field K] [Fintype T] {V W : T → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, FiniteDimensional K (V i)] [∀ i, FiniteDimensional K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (c : T → ℕ)
    (hc : ∀ i, Module.finrank K (W i) ≤ Module.finrank K (LinearMap.range (f i)) + c i) :
    Module.finrank K (∀ i, W i) ≤ Module.finrank K (LinearMap.range (familyMap f)) + ∑ i, c i

axiom codimension_map_le {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (S : Submodule K V) :
    Module.finrank K W - Module.finrank K (S.map f) ≤ Module.finrank K V - Module.finrank K S

open Lax342547.MomentSpace
open scoped ENNReal

axiom uniform_image_bound {V W : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W] [Fintype V] [Fintype W]
    [FiniteDimensional Binary V] [FiniteDimensional Binary W]
    (f : V →ₗ[Binary] W) (c : ℕ)
    (hc : Module.finrank Binary W ≤ Module.finrank Binary (LinearMap.range f) + c) (y : W) :
    (PMF.uniformOfFintype V).map f y ≤ 2 ^ c * PMF.uniformOfFintype W y

axiom uniform_image_of_surjective {V W : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W] [Fintype V] [Fintype W]
    [FiniteDimensional Binary V] [FiniteDimensional Binary W]
    (f : V →ₗ[Binary] W) (hf : Function.Surjective f) :
    (PMF.uniformOfFintype V).map f = PMF.uniformOfFintype W

axiom uniform_affine_image_bound {V W : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W] [Fintype V]
    [FiniteDimensional Binary V]
    (f : V →ₗ[Binary] W) (a y : W) (r : ℕ)
    (hr : r ≤ Module.finrank Binary (LinearMap.range f)) :
    (PMF.uniformOfFintype V).map (fun x => a + f x) y ≤ 1 / (2 : ℝ≥0∞) ^ r

end Lax342547.FiniteLinearLaw
