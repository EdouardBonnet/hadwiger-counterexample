import Lax342547.QuotientRank
import Lax342547Proofs.RestrictionRank

namespace Lax342547Proofs.QuotientRank

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.QuotientRank.killed_composition_rank
---
Restrict the middle map to the image of the right map. Its image is in
the left kernel; restriction costs at most the right-image codimension.
-/
theorem killed_composition_rank {K U V W X : Type} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (A : W →ₗ[K] X) (M : V →ₗ[K] W) (B : U →ₗ[K] V)
    (h : A.comp (M.comp B) = 0) :
    Module.finrank K (LinearMap.range M) ≤
      Module.finrank K (LinearMap.ker A) +
        (Module.finrank K V - Module.finrank K (LinearMap.range B)) := by
  have hr := RestrictionRank.domain_restriction_rank M (LinearMap.range B)
  have heq : LinearMap.range (M.comp (LinearMap.range B).subtype) =
      LinearMap.range (M.comp B) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.range_comp]
  have hle : LinearMap.range (M.comp B) ≤ LinearMap.ker A := by
    rintro _ ⟨u, rfl⟩
    exact LinearMap.congr_fun h u
  rw [heq] at hr
  exact hr.trans (Nat.add_le_add_right (Submodule.finrank_mono hle) _)

/--
---
conclusion: Lax342547.QuotientRank.killed_matrix_rank
---
Apply the linear-map bound to the matrix sandwich. Rank-nullity and
invariance under transpose identify its right loss with the second kernel.
-/
theorem killed_matrix_rank {K I J P Q : Type} [Field K]
    [Fintype I] [Fintype J] [Fintype P] [Fintype Q]
    (A : Matrix P I K) (M : Matrix I J K) (B : Matrix Q J K)
    (h : A * M * B.transpose = 0) :
    M.rank ≤ Module.finrank K (LinearMap.ker A.mulVecLin) +
      Module.finrank K (LinearMap.ker B.mulVecLin) := by
  have hc : A.mulVecLin.comp (M.mulVecLin.comp B.transpose.mulVecLin) = 0 := by
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, ← Matrix.mul_assoc, h]
    simp
  have hr := Lax342547.QuotientRank.killed_composition_rank A.mulVecLin M.mulVecLin B.transpose.mulVecLin hc
  have hn := B.mulVecLin.finrank_range_add_finrank_ker
  have ht : Module.finrank K (LinearMap.range B.transpose.mulVecLin) =
      Module.finrank K (LinearMap.range B.mulVecLin) := Matrix.rank_transpose B
  rw [ht] at hr
  change Module.finrank K (LinearMap.range M.mulVecLin) ≤ _
  simp only [Module.finrank_pi] at hr hn
  omega

/--
---
conclusion: Lax342547.QuotientRank.killed_quotients_rank
---
The kernel of the left quotient is its subspace. The right quotient's
dual image is its annihilator, whose codimension is the subspace dimension.
-/
theorem killed_quotients_rank {K V W : Type} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (M : Module.Dual K V →ₗ[K] W) (S : Submodule K W) (T : Submodule K V)
    (h : S.mkQ.comp (M.comp T.mkQ.dualMap) = 0) :
    Module.finrank K (LinearMap.range M) ≤ Module.finrank K S + Module.finrank K T := by
  have hr := Lax342547.QuotientRank.killed_composition_rank S.mkQ M T.mkQ.dualMap h
  rw [Submodule.ker_mkQ, T.range_dualMap_mkQ_eq, Subspace.dual_finrank_eq] at hr
  have ht := Subspace.finrank_add_finrank_dualAnnihilator_eq T
  omega

end Lax342547Proofs.QuotientRank
