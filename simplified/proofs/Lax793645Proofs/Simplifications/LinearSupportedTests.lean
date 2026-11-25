import Lax793645Proofs.Simplifications.LinearTestPartitions
import Lax793645Proofs.Simplifications.GramFourCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A bounded test is replaced by a bounded function of finitely many
linear equations. Its residual, extended by zero off the prescribed key
variety, has small Fourier coefficients. -/
theorem linear_supported_test (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ k : ℕ,∀ (I : Type) [Fintype I] [DecidableEq I]
      (K : Vec I→Prop) (f : Wgt (Vec I)),(∀ x,|f x|≤B) →
      ∃ r : ℕ,r≤k ∧ ∃ P : Mat (Fin r) I,∃ φ : Wgt (Vec (Fin r)),
        (∀ y,|φ y|≤B) ∧ ∀ ξ : Vec I,
          |linearFourier (fun x=>(f x-φ (P*ᵥx))*ind (K x)) ξ|≤δ := by
  classical
  obtain ⟨k,hk⟩:=linear_test_partition B δ hB hδ
  refine ⟨k,fun I _ _ K f hf=>?_⟩
  obtain ⟨r,hr,P,hP⟩:=hk I (unifOn K) (unifOn_sub K) f hf
  let φ:=cashbook (unifOn K) P.mulVec f
  refine ⟨r,hr,P,φ,cashbook_bound (unifOn K) (unifOn_sub K).nz P.mulVec f B hB hf,?_⟩
  intro ξ
  by_cases hK : ∃ x,K x
  · obtain ⟨x,hx⟩:=hK
    have hmass : 0<pr (unif : Wgt (Vec I)) K:=by
      have hh:=weight_le_pr unif_law.nz hx
      have hx0 : (0:ℝ)<unif x:=by rw [unif_apply]; positivity
      exact hx0.trans_le hh
    have hm1 : pr (unif : Wgt (Vec I)) K≤1:=
      (pr_le_tot unif_law.nz).trans_eq unif_law.total
    have he : linearFourier (fun x=>(f x-φ (P*ᵥx))*ind (K x)) ξ=
        pr unif K*dip (unifOn K) (fun x=>f x-banner (unifOn K) P.mulVec f x) (vectorPhase ξ):=by
      unfold dip
      rw [←part_reset K _ hmass]
      unfold linearFourier partMean
      apply avg_congr
      intro x _
      change vectorPhase ξ x*((f x-φ (P*ᵥx))*ind (K x))=
        ind (K x)*((f x-φ (P*ᵥx))*vectorPhase ξ x)
      ring
    rw [he,abs_mul,abs_of_pos hmass]
    exact (mul_le_mul_of_nonneg_left (hP ξ) hmass.le).trans
      ((mul_le_mul_of_nonneg_right hm1 hδ.le).trans_eq (one_mul δ))
  · have hz : ∀ x,ind (K x)=0:=fun x=>ind_zero (fun hx=>hK ⟨x,hx⟩)
    simp only [linearFourier,hz,mul_zero,avg_zero,abs_zero]
    exact hδ.le

end
end Lax793645Proofs.Simplifications
