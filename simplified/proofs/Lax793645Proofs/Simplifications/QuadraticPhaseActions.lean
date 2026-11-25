import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MatrixRankCounting

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A H D : Type} [Fintype A] [Fintype H] [Fintype D]
  [DecidableEq A] [DecidableEq H] [DecidableEq D]

/-- Polar action of the channel quadratic form on a list of cover vectors,
linear in the freely sampled second channel matrix. -/
def quadraticPhaseAction (X : Mat A H) (T : Mat A D) : Mat A H→ₗ[F]Mat A D where
  toFun Y:=Y*(Xᵀ*T)+X*(Yᵀ*T)
  map_add' Y Z:=by simp only [Matrix.add_mul,Matrix.transpose_add,Matrix.mul_add]; abel
  map_smul' c Y:=by simp only [Matrix.smul_mul,Matrix.transpose_smul,Matrix.mul_smul,smul_add,RingHom.id_apply]

/-- Full rank of the first-channel evaluation leaves at least d(N-h)
independent polar constraints on the second channel matrix. -/
theorem quadratic_phase_action_rank (X : Mat A H) (T : Mat A D)
    (hXT : Function.Injective (Xᵀ*T).mulVec) :
    Fintype.card A*Fintype.card D≤rk (quadraticPhaseAction X T)+
      Fintype.card H*Fintype.card D := by
  let U : Mat A H→ₗ[F]Mat A D:=rmult A (Xᵀ*T)
  let V : Mat A H→ₗ[F]Mat H D:={
    toFun Y:=Yᵀ*T
    map_add' _ _:=by simp only [Matrix.transpose_add,Matrix.add_mul]
    map_smul' _ _:=by simp only [Matrix.transpose_smul,Matrix.smul_mul,RingHom.id_apply] }
  let L : Mat H D→ₗ[F]Mat A D:={
    toFun Y:=X*Y
    map_add' _ _:=Matrix.mul_add ..
    map_smul' _ _:=Matrix.mul_smul .. }
  have hu : Function.Surjective U := by
    obtain ⟨B,hB⟩:=mat_left_inv hXT
    intro C
    refine ⟨C*B,?_⟩
    change C*B*(Xᵀ*T)=C
    rw [Matrix.mul_assoc,hB,Matrix.mul_one]
  have he : U=quadraticPhaseAction X T+L.comp V := by
    ext Y a d
    change (Y*(Xᵀ*T)) a d=((Y*(Xᵀ*T)) a d+(X*(Yᵀ*T)) a d)+(X*(Yᵀ*T)) a d
    rw [add_assoc,char_two,add_zero]
  have hr:=rk_add_le (quadraticPhaseAction X T) (L.comp V)
  rw [←he,rk_surj.mp hu,dim_mat] at hr
  have hl : rk (L.comp V)≤Fintype.card H*Fintype.card D := by
    apply (rk_comp_le_right V L).trans
    have hv:=Submodule.finrank_le V.range
    simpa only [rk,dim_mat] using hv
  omega

/-- Point mass for the polar action, with no enumeration of quadratic
forms or orthogonal group needed. -/
theorem quadratic_phase_action_cap (X : Mat A H) (T : Mat A D)
    (hXT : Function.Injective (Xᵀ*T).mulVec) (B : Mat A D) :
    pr unif (fun Y=>quadraticPhaseAction X T Y=B)≤
      bp (-((num A-num H)*num D)) := by
  rw [pr_unif_lin]
  apply (mul_le_mul_of_nonneg_right (ind_le_one _) (bp_pos _).le).trans
  rw [one_mul]
  apply bp_le
  have hh:=quadratic_phase_action_rank X T hXT
  have hh' : num A*num D≤(rk (quadraticPhaseAction X T):ℝ)+num H*num D := by
    exact_mod_cast hh
  nlinarith

end
end Lax793645Proofs.Simplifications
