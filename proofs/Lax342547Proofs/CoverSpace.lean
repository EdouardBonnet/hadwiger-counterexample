import Lax342547.CoverSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

namespace Lax342547Proofs.CoverSpace
open Lax342547.CoverSpace

set_option backward.isDefEq.respectTransparency false
open Lax342547.CoverProjection

/--
---
conclusion: Lax342547.CoverSpace.covered_decomposition
---
-/
theorem covered_decomposition {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (M : V →ₗ[K] W) (hM : projection M S T = 0) :
    M ∈ LinearMap.range (coverAssembly S T) := by
  obtain ⟨π,hπ⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  let A := π.comp M
  let D := M-S.subtype.comp A
  have hker : T.dualCoannihilator ≤ LinearMap.ker D := by
    intro v hv
    have hh := congrArg (fun f : T.dualCoannihilator →ₗ[K] (W ⧸ S) => f ⟨v,hv⟩) hM
    have hm : M v ∈ S := by
      change S.mkQ (M v) = 0 at hh
      rw [← Submodule.ker_mkQ S]
      exact LinearMap.mem_ker.mpr hh
    have hp := congrArg (fun f : S →ₗ[K] S => f ⟨M v,hm⟩) hπ
    change π (M v) = ⟨M v,hm⟩ at hp
    change M v-S.subtype (π (M v)) = 0
    rw [hp]
    simp
  let B := T.dualCoannihilator.liftQ D hker
  refine ⟨(A,B),?_⟩
  change S.subtype.comp A+B.comp T.dualCoannihilator.mkQ = M
  rw [show B.comp T.dualCoannihilator.mkQ = D from T.dualCoannihilator.liftQ_mkQ D hker]
  dsimp [D]
  abel

/--
---
conclusion: Lax342547.CoverSpace.cover_space_dimension
---
-/
theorem cover_space_dimension {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V)) :
    Module.finrank K (LinearMap.ker (coverOperator S T)) ≤
      Module.finrank K V*Module.finrank K S+Module.finrank K T*Module.finrank K W := by
  have hle : LinearMap.ker (coverOperator S T) ≤ LinearMap.range (coverAssembly S T) := by
    intro M hM
    exact Lax342547.CoverSpace.covered_decomposition S T M hM
  have hh := (Submodule.finrank_mono hle).trans (coverAssembly S T).finrank_range_le
  have ht : Module.finrank K (V ⧸ T.dualCoannihilator) = Module.finrank K T := by
    have ha := Submodule.finrank_quotient_add_finrank T.dualCoannihilator
    have hb := Subspace.finrank_add_finrank_dualCoannihilator_eq T
    omega
  simpa only [Module.finrank_prod,Module.finrank_linearMap,ht] using hh

end Lax342547Proofs.CoverSpace
