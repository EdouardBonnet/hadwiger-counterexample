import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions

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

end Lax342547.FiniteLinearLaw
