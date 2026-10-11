import Lax342547.RankLoss
import Lax342547Proofs.RestrictionRank
import Lax342547Proofs.QuotientRank

namespace Lax342547Proofs.RankLoss
open Lax342547.RankLoss

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.RankLoss.composition_rank_loss
---
-/
theorem composition_rank_loss {K U V W X : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (A : W →ₗ[K] X) (M : V →ₗ[K] W) (B : U →ₗ[K] V) :
    Module.finrank K (LinearMap.range M) ≤
      Module.finrank K (LinearMap.range (A.comp (M.comp B))) +
        Module.finrank K (LinearMap.ker A) +
        (Module.finrank K V-Module.finrank K (LinearMap.range B)) := by
  have hr := Lax342547Proofs.RestrictionRank.domain_restriction_rank M (LinearMap.range B)
  have heq : LinearMap.range (M.comp (LinearMap.range B).subtype) = LinearMap.range (M.comp B) := by
    rw [LinearMap.range_comp,Submodule.range_subtype,LinearMap.range_comp]
  rw [heq] at hr
  have hl := Lax342547Proofs.RestrictionRank.finrank_le_map_add_ker A (LinearMap.range (M.comp B))
  rw [← LinearMap.range_comp] at hl
  omega

/--
---
conclusion: Lax342547.RankLoss.matrix_sandwich_rank_loss
---
-/
theorem matrix_sandwich_rank_loss {K I J P Q : Type} [Field K]
    [Fintype I] [Fintype J] [Fintype P] [Fintype Q]
    (A : Matrix P I K) (M : Matrix I J K) (B : Matrix Q J K) :
    M.rank ≤ (A*M*B.transpose).rank +
      Module.finrank K (LinearMap.ker A.mulVecLin) +
      Module.finrank K (LinearMap.ker B.mulVecLin) := by
  have hr := composition_rank_loss A.mulVecLin M.mulVecLin B.transpose.mulVecLin
  have hn := B.mulVecLin.finrank_range_add_finrank_ker
  have ht : Module.finrank K (LinearMap.range B.transpose.mulVecLin) =
      Module.finrank K (LinearMap.range B.mulVecLin) := Matrix.rank_transpose B
  rw [ht] at hr
  rw [← Matrix.mulVecLin_mul,← Matrix.mulVecLin_mul,← Matrix.mul_assoc] at hr
  change Module.finrank K (LinearMap.range M.mulVecLin) ≤ _
  simp only [Module.finrank_pi] at hr hn
  unfold Matrix.rank
  omega

/--
---
conclusion: Lax342547.RankLoss.quotient_tensor_rank_loss
---
-/
theorem quotient_tensor_rank_loss {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : Module.Dual K V →ₗ[K] W) (S : Submodule K W) (T : Submodule K V) :
    Module.finrank K (LinearMap.range M) ≤
      Module.finrank K (LinearMap.range (S.mkQ.comp (M.comp T.mkQ.dualMap))) +
      Module.finrank K S+Module.finrank K T := by
  have hr := composition_rank_loss S.mkQ M T.mkQ.dualMap
  rw [Submodule.ker_mkQ,T.range_dualMap_mkQ_eq,Subspace.dual_finrank_eq] at hr
  have ht := Subspace.finrank_add_finrank_dualAnnihilator_eq T
  omega

end Lax342547Proofs.RankLoss
