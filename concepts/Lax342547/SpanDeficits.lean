import Lax342547.RestrictionRank
import Mathlib.LinearAlgebra.Pi

/-!
---
title: Mode space span deficits
type: definition and theorem
---
The kernel dimension of the addition map is the difference between the sum of component dimensions and the dimension of their span.
-/

namespace Lax342547.SpanDeficits

open scoped BigOperators

noncomputable def addition {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) : (∀ i, S i) →ₗ[K] V := by
  classical
  exact LinearMap.lsum K (fun i => S i) K (fun i => (S i).subtype)

axiom addition_single {K V ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) (i : ι) (v : S i) :
    addition S (Pi.single i v) = v.val

axiom addition_range {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] (S : ι → Submodule K V) :
    LinearMap.range (addition S) = ⨆ i, S i

axiom addition_kernel_deficit {K V ι : Type} [Field K] [Fintype ι]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (S : ι → Submodule K V) :
    Module.finrank K (LinearMap.ker (addition S)) =
      (∑ i, Module.finrank K (S i))-Module.finrank K (⨆ i, S i : Submodule K V)

end Lax342547.SpanDeficits
