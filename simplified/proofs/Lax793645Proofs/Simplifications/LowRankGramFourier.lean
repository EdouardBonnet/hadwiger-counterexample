import Lax793645Proofs.Simplifications.GramFourCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

/-- A slot-rank-r Gram phase has Fourier norm at most 2^(Nr), including
singular matrices. It only depends on 2Nr ambient binary coordinates. -/
theorem low_rank_gram_fourier_norm (M : Mat I I) :
    fourierNorm (fun x : KeyCoordinates I N=>wsign (gramPrimitive M x))≤
      bp ((N:ℝ)*M.rank) := by
  obtain ⟨A,B,_,_,hM⟩ := rank_product M
  let P : KeyCoordinates I N→ₗ[F] PlusRack (Fin M.rank) N :=
    (rmult (Fin N) A).comp keyPlus
  let Q : KeyCoordinates I N→ₗ[F] PlusRack (Fin M.rank) N :=
    (rmult (Fin N) Bᵀ).comp keyMinus
  let T : KeyCoordinates I N→ₗ[F] KeyCoordinates (Fin M.rank) N :=
    (keyInsert false).comp P+(keyInsert true).comp Q
  have hp x : keyPlus (T x)=keyPlus x*A := by
    simp only [T,LinearMap.add_apply,LinearMap.comp_apply,map_add,
      plus_insert_false,plus_insert_true,add_zero]
    rfl
  have hq x : keyMinus (T x)=keyMinus x*Bᵀ := by
    simp only [T,LinearMap.add_apply,LinearMap.comp_apply,map_add,
      minus_insert_false,minus_insert_true,zero_add]
    rfl
  let w : Wgt (KeyCoordinates (Fin M.rank) N) := fun x=>wsign (gramPrimitive 1 x)
  have he x : w (T x)=wsign (gramPrimitive M x) := by
    dsimp only [w,gramPrimitive]
    rw [hp,hq]
    congr 1
    change ((keyPlus x*A)*(1 : Mat (Fin M.rank) (Fin M.rank))*(keyMinus x*Bᵀ)ᵀ).trace=(keyPlus x*M*(keyMinus x)ᵀ).trace
    rw [Matrix.mul_one,Matrix.transpose_mul,Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [←Matrix.mul_assoc A B,hM]
  have hh := fourier_norm_linear_pullback (LinearMap.toMatrix' T) w
  have ht x : (LinearMap.toMatrix' T)*ᵥx=T x := LinearMap.congr_fun (toMat_map T) x
  simp only [ht,he] at hh
  refine hh.trans ((fourier_norm_bounded w (fun x=>wsign_abs _ |>.le)).trans_eq ?_)
  congr 1
  simp only [num,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
  ring

end
end Lax793645Proofs.Simplifications
