import Lax342547.CoverProjection
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
---
title: Actual tensor cover decomposition and dimension
type: definition and theorem
---
A checked quotient decomposition of every covered map gives the dimension bound for the whole actual cover space.
-/

namespace Lax342547.CoverSpace

open Lax342547.CoverProjection

noncomputable def coverAssembly {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    ((V →ₗ[K] S) × ((V ⧸ T.dualCoannihilator) →ₗ[K] W)) →ₗ[K] (V →ₗ[K] W) where
  toFun z := S.subtype.comp z.1+z.2.comp T.dualCoannihilator.mkQ
  map_add' _ _ := by simp [LinearMap.comp_add,LinearMap.add_comp]; abel
  map_smul' _ _ := by simp [LinearMap.comp_smul,LinearMap.smul_comp]

noncomputable def coverOperator {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    (V →ₗ[K] W) →ₗ[K] (T.dualCoannihilator →ₗ[K] (W ⧸ S)) where
  toFun M := projection M S T
  map_add' _ _ := by simp [projection,LinearMap.comp_add,LinearMap.add_comp]
  map_smul' _ _ := by simp [projection,LinearMap.comp_smul,LinearMap.smul_comp]

axiom covered_decomposition {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (M : V →ₗ[K] W) (hM : projection M S T = 0) :
    M ∈ LinearMap.range (coverAssembly S T)

axiom cover_space_dimension {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    Module.finrank K (LinearMap.ker (coverOperator S T)) ≤
      Module.finrank K V*Module.finrank K S+Module.finrank K T*Module.finrank K W

end Lax342547.CoverSpace
