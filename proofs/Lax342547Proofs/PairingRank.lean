import Lax342547.PairingRank
import Lax342547Proofs.CoverSpace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Finsupp.LSum

namespace Lax342547Proofs.PairingRank
open Lax342547.PairingRank

set_option backward.isDefEq.respectTransparency false
open Lax342547.CoverProjection
open scoped BigOperators

/--
---
conclusion: Lax342547.PairingRank.pairing_matrix_rank_le
---
-/
theorem pairing_matrix_rank_le {K V Ω : Type} [Field K] [Fintype Ω]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Submodule K V) (v : Ω → V) (hv : ∀ a, v a ∈ S) (φ : Ω → Module.Dual K V) :
    (Matrix.of (fun a b => φ b (v a))).rank ≤ Module.finrank K S := by
  classical
  let A : (Ω → K) →ₗ[K] S := LinearMap.lsum K (fun _ : Ω => K) K
    (fun a => LinearMap.toSpanSingleton K S ⟨v a,hv a⟩)
  let B : S →ₗ[K] (Ω → K) := LinearMap.pi (fun b => (φ b).comp S.subtype)
  have he : (Matrix.of (fun a b => φ b (v a))).transpose.mulVecLin = B.comp A := by
    apply LinearMap.ext
    intro x
    ext b
    simp [Matrix.mulVecLin_apply,Matrix.mulVec,Matrix.vecMul,dotProduct,Matrix.transpose_apply,A,B,
      LinearMap.lsum_apply,LinearMap.toSpanSingleton_apply,map_sum,map_smul]
  rw [← Matrix.rank_transpose,Matrix.rank,he]
  apply (Submodule.finrank_mono (show LinearMap.range (B.comp A) ≤ LinearMap.range B from by
    rw [LinearMap.range_comp]; exact LinearMap.map_le_range)).trans
  exact B.finrank_range_le

/--
---
conclusion: Lax342547.PairingRank.covered_pairing_rank
---
-/
theorem covered_pairing_rank {K V W Ω : Type} [Field K] [Fintype Ω]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K W) (T : Submodule K (Module.Dual K V))
    (Δ : Ω → V →ₗ[K] W) (φ : Ω → Module.Dual K (V →ₗ[K] W))
    (hΔ : ∀ a, projection (Δ a) S T = 0) :
    (Matrix.of (fun a b => φ b (Δ a))).rank ≤
      Module.finrank K V*Module.finrank K S+Module.finrank K T*Module.finrank K W := by
  exact (pairing_matrix_rank_le (LinearMap.ker (Lax342547.CoverSpace.coverOperator S T)) Δ hΔ φ).trans
    (Lax342547Proofs.CoverSpace.cover_space_dimension S T)

end Lax342547Proofs.PairingRank
