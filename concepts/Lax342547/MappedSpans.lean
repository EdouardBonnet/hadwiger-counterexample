import Lax342547.ActualDeficits

/-!
---
title: Dimension deficits after an arbitrary mode map
type: lemma
---
Actual mapped mode dimensions equal their increments modulo the map kernel; mapped span deficits therefore equal the corresponding exposure deficits.
-/

namespace Lax342547.MappedSpans

open Lax342547.GreedySpans Lax342547.GreedyTails
open scoped BigOperators

axiom mapped_dimension_gain {K V U : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U] [FiniteDimensional K V]
    (f : V →ₗ[K] U) (S : Submodule K V) :
    (Module.finrank K (S.map f) : ℝ) = gain (LinearMap.ker f) S

noncomputable def mappedDeficit {K V U ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U] [FiniteDimensional K V]
    (S : ι → Submodule K V) (f : V →ₗ[K] U) (l : List ι) : ℝ :=
    (l.map (fun i => (Module.finrank K ((S i).map f) : ℝ))).sum-
      Module.finrank K (l.toFinset.sup (fun i => (S i).map f) : Submodule K U)

axiom mapped_deficit_eq {K V U ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U] [FiniteDimensional K V]
    (S : ι → Submodule K V) (f : V →ₗ[K] U) (l : List ι) :
    mappedDeficit S f l = deficit S (LinearMap.ker f) l

end Lax342547.MappedSpans
