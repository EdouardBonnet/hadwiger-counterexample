import Lax342547.SymmetricFactorization
import Lax342547Proofs.MixerCompatibility
import Lean.Elab.Tactic.Omega
import Lax342547.LowRankCounting

namespace Lax342547Proofs.SymmetricFactorization

set_option backward.isDefEq.respectTransparency false

variable {K I J : Type} [Field K] [Fintype I] [Fintype J]

omit [Fintype I] in
theorem injective_of_rank_eq_width (M : Matrix I J K) (hM : M.rank = Fintype.card J) :
    Function.Injective M.mulVec := by
  change Function.Injective M.mulVecLin
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have hd := M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank + Module.finrank K (LinearMap.ker M.mulVecLin) = Module.finrank K (J → K) at hd
  rw [hM, Module.finrank_fintype_fun_eq_card] at hd
  omega

/--
---
conclusion: Lax342547.SymmetricFactorization.symmetric_factorization
---
Factor M through its rank and take a left inverse U of the first factor Z.
Put H=UMUᵀ. The projection ZU fixes M on the left and, by symmetry, on
the right, proving ZHZᵀ=M. The rank of M forces H to be nonsingular.
-/
theorem symmetric_factorization (M : Matrix I I K) (hM : M.transpose = M) :
    ∃ Z : Matrix I (Fin M.rank) K, ∃ H : Matrix (Fin M.rank) (Fin M.rank) K,
      Function.Injective Z.mulVec ∧ H.transpose = H ∧ Function.Bijective H.mulVec ∧
      Z * H * Z.transpose = M := by
  classical
  obtain ⟨Z, Y, hZY⟩ := Lax342547.LowRankCounting.factorization M M.rank le_rfl
  have hZrank : Z.rank = M.rank := by
    apply le_antisymm
    · simpa using Z.rank_le_card_width
    · exact (congrArg Matrix.rank hZY).symm.trans_le (Matrix.rank_mul_le_left Z Y)
  have hZ : Function.Injective Z.mulVec := injective_of_rank_eq_width Z (by simpa using hZrank)
  obtain ⟨U, hU⟩ := MixerCompatibility.exists_left_inverse Z hZ
  have hp : Z * U * M = M := calc
    _ = Z * U * (Z * Y) := congrArg (fun A : Matrix I I K => Z * U * A) hZY.symm
    _ = Z * (U * Z) * Y := by simp only [Matrix.mul_assoc]
    _ = M := by rw [hU, Matrix.mul_one, hZY]
  have hpt : M * U.transpose * Z.transpose = M := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hM, Matrix.mul_assoc]
      using congrArg Matrix.transpose hp
  let H := U * M * U.transpose
  have hfactor : Z * H * Z.transpose = M := calc
    _ = (Z * U * M) * U.transpose * Z.transpose := by simp only [H, Matrix.mul_assoc]
    _ = M := by rw [hp, hpt]
  have hHrank : H.rank = M.rank := by
    apply le_antisymm
    · simpa using H.rank_le_card_width
    · exact (congrArg Matrix.rank hfactor).symm.trans_le
        ((Matrix.rank_mul_le_left (Z * H) Z.transpose).trans (Matrix.rank_mul_le_right Z H))
  have hH : Function.Injective H.mulVec := injective_of_rank_eq_width H (by simpa using hHrank)
  refine ⟨Z, H, hZ, ?_, ⟨hH, ?_⟩, hfactor⟩
  · simp only [H, Matrix.transpose_mul, Matrix.transpose_transpose, hM, Matrix.mul_assoc]
  · exact (LinearMap.injective_iff_surjective (f := H.mulVecLin)).mp hH

open Lax342547.MomentSpace

/--
---
conclusion: Lax342547.SymmetricFactorization.card_symmetric_rank
---
Choose a rank-r symmetric factorization for each matrix. Its two factors
encode the original matrix and use |I|r+r² binary entries.
-/
theorem card_symmetric_rank {I : Type} [Fintype I] (r : ℕ) :
    Nat.card {M : Matrix I I Binary // M.transpose = M ∧ M.rank = r} ≤
      2 ^ (Fintype.card I * r + r * r) := by
  classical
  let T := {M : Matrix I I Binary // M.transpose = M ∧ M.rank = r}
  have hf (M : T) : ∃ Z : Matrix I (Fin r) Binary, ∃ H : Matrix (Fin r) (Fin r) Binary,
      Z * H * Z.transpose = M.val := by
    rcases M with ⟨M, hM, hr⟩
    change ∃ Z : Matrix I (Fin r) Binary, ∃ H : Matrix (Fin r) (Fin r) Binary,
      Z * H * Z.transpose = M
    subst r
    obtain ⟨Z, H, _, _, _, h⟩ := Lax342547.SymmetricFactorization.symmetric_factorization M hM
    exact ⟨Z, H, h⟩
  choose Z H hZH using hf
  have hi : Function.Injective (fun M : T => (Z M, H M)) := by
    intro M N he
    apply Subtype.ext
    rw [← hZH M, ← hZH N, (Prod.mk.inj he).1, (Prod.mk.inj he).2]
  calc
    Nat.card T = Fintype.card T := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (Matrix I (Fin r) Binary × Matrix (Fin r) (Fin r) Binary) :=
      Fintype.card_le_of_injective _ hi
    _ = _ := by
      change Fintype.card ((I → Fin r → Binary) × (Fin r → Fin r → Binary)) = _
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Binary, ZMod.card,
        ← pow_mul, ← pow_add]
      congr 1
      ring

end Lax342547Proofs.SymmetricFactorization
