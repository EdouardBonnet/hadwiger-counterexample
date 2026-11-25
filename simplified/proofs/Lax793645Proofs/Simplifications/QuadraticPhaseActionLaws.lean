import Lax793645Proofs.Simplifications.QuadraticPhaseActions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A H D : Type} [Fintype A] [Fintype H] [Fintype D]
  [DecidableEq A] [DecidableEq H] [DecidableEq D]

def channelEvaluation (T : Mat A D) : Mat A H→ₗ[F]Mat H D where
  toFun X:=Xᵀ*T
  map_add' _ _:=by simp only [Matrix.transpose_add,Matrix.add_mul]
  map_smul' _ _:=by simp only [Matrix.transpose_smul,Matrix.smul_mul,RingHom.id_apply]

theorem channel_evaluation_surjective (T : Mat A D) (hT : Function.Injective T.mulVec) :
    Function.Surjective (channelEvaluation (H:=H) T) := by
  obtain ⟨B,hB⟩:=mat_left_inv hT
  intro C
  refine ⟨(C*B)ᵀ,?_⟩
  change ((C*B)ᵀ)ᵀ*T=C
  rw [Matrix.transpose_transpose,Matrix.mul_assoc,hB,Matrix.mul_one]

/-- Failure of full channel evaluation rank is paid only at the fixed
channel scale. The ambient dimension does not enter this loss. -/
theorem quadratic_phase_glimpse_failure (T : Mat A D) (hT : Function.Injective T.mulVec) :
    pr unif (fun X : Mat A H=>¬Function.Injective (Xᵀ*T).mulVec)≤bp (num D-num H) := by
  have he : (fun X : Mat A H=>¬Function.Injective (Xᵀ*T).mulVec)=
      fun X=>((channelEvaluation T X).rank+1≤Fintype.card D) := by
    funext X
    apply propext
    rw [mrk_inj]
    have hh:=Matrix.rank_le_card_width (channelEvaluation (H:=H) T X)
    change ¬(channelEvaluation T X).rank=Fintype.card D↔_
    omega
  rw [he,←mapW_pr unif (channelEvaluation (H:=H) T)
    (fun M=>M.rank+1≤Fintype.card D),map_unif_surjective _ (channel_evaluation_surjective T hT)]
  simpa using (pr_deficient (I:=H) (J:=D) 1)

/-- The target may depend on the first channel matrix. Full rank is
retained inside the event, so no additive rank-failure error is introduced. -/
theorem quadratic_phase_pair_cap (T : Mat A D) (B : Mat A H→Mat A D) :
    pr (pairW unif unif) (fun xy : Mat A H×Mat A H=>
      Function.Injective (xy.1ᵀ*T).mulVec ∧ quadraticPhaseAction xy.1 T xy.2=B xy.1)≤
      bp (-((num A-num H)*num D)) := by
  rw [pr,pairW_avg]
  apply unif_law.avg_le
  intro X
  by_cases hx : Function.Injective (Xᵀ*T).mulVec
  · simp only [hx,true_and]
    exact quadratic_phase_action_cap X T hx (B X)
  simp only [hx,false_and,ind_false,avg_zero]
  exact (bp_pos _).le

/-- Capped channel laws inherit the same unnormalized point bound. -/
theorem quadratic_phase_read_cap {Ω : Type} [Fintype Ω] (w : Wgt Ω)
    (read : Ω→Mat A H×Mat A H) {C : ℝ} (hC : 0≤C)
    (hread : ∀ x,mapW w read x≤C*pairW unif unif x)
    (T : Mat A D) (B : Mat A H→Mat A D) :
    pr w (fun o=>Function.Injective ((read o).1ᵀ*T).mulVec ∧
      quadraticPhaseAction (read o).1 T (read o).2=B (read o).1)≤
      C*bp (-((num A-num H)*num D)) := by
  have he:=pr_cap hread (fun xy=>Function.Injective (xy.1ᵀ*T).mulVec ∧
    quadraticPhaseAction xy.1 T xy.2=B xy.1)
  rw [mapW_pr] at he
  exact he.trans (mul_le_mul_of_nonneg_left (quadratic_phase_pair_cap T B) hC)

end
end Lax793645Proofs.Simplifications
