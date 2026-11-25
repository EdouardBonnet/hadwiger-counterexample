import Lax793645Proofs.Simplifications.LinearSupportedTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Starting from any prescribed partition, a bounded number of added
linear equations makes the bounded test's Fourier residual small. The
number of added equations is independent of the starting partition. -/
theorem linear_test_refinement (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ k : ℕ,∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J]
      (μ : Wgt (Vec I)),SubLaw μ → ∀ (f : Wgt (Vec I)) (Q : Vec I→J),
      (∀ x,|f x|≤B) →
      ∃ r : ℕ,r≤k ∧ ∃ P : Mat (Fin r) I,
        ∀ ξ : Vec I,|dip μ (fun x=>f x-banner μ (fun x=>(Q x,P*ᵥx)) f x)
          (vectorPhase ξ)|≤δ := by
  obtain ⟨k,hk⟩:=exists_nat_gt (B^2/δ^2)
  rw [div_lt_iff₀ (sq_pos_of_pos hδ)] at hk
  refine ⟨k,fun I J _ _ _ μ hμ f Q hf=>?_⟩
  by_contra! h
  have he (r : ℕ) (hr : r≤k) : ∃ P : Mat (Fin r) I,
      (r:ℝ)*δ^2≤ode μ (banner μ (fun x=>(Q x,P*ᵥx)) f) := by
    induction r with
    | zero =>
      refine ⟨0,?_⟩
      simp only [Nat.cast_zero,zero_mul]
      exact ode_nonneg hμ.nz _
    | succ r ih =>
      obtain ⟨P,hP⟩:=ih (by omega)
      obtain ⟨ξ,hξ⟩:=h r (by omega) P
      let R : Mat (Fin (r+1)) I:=Fin.cons ξ P
      let F (x : Vec I):=(Q x,R*ᵥx)
      let G (x : J×Vec (Fin (r+1))) : J×Vec (Fin r):=(x.1,fun i=>x.2 i.succ)
      let w (x : J×Vec (Fin (r+1))) : ℝ:=wsign (x.2 0)
      have hG : G∘F=(fun x=>(Q x,P*ᵥx)):=rfl
      have hw : w∘F=vectorPhase ξ:=rfl
      have hgain:=archive_gain hμ f F G w (fun x=>by dsimp [w]; exact (wsign_abs _).le)
      rw [hG,hw] at hgain
      have hsq:=sq_le_sq₀ hδ.le (abs_nonneg _) |>.mpr hξ.le
      rw [sq_abs] at hsq
      refine ⟨R,?_⟩
      push_cast
      linarith only [hP,hgain,hsq]
  obtain ⟨P,hP⟩:=he k le_rfl
  have hb x : |banner μ (fun x=>(Q x,P*ᵥx)) f x|≤B:=
    cashbook_bound μ hμ.nz _ f B hB hf _
  exact (not_lt_of_ge (hP.trans (ode_upper hμ _ B hb))) hk

/-- The actual approximant is the conditional average on the refined
partition. Its orthogonality to the old cells is retained exactly. -/
theorem linear_supported_refinement (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ k : ℕ,∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J]
      (K : Vec I→Prop) (f : Wgt (Vec I)) (Q : Vec I→J),
      (∀ x,|f x|≤B) →
      ∃ r : ℕ,r≤k ∧ ∃ P : Mat (Fin r) I,
        let S:=banner (unifOn K) (fun x=>(Q x,P*ᵥx)) f
        (∀ x,|S x|≤B) ∧
        ∀ ξ,|linearFourier (fun x=>(f x-S x)*ind (K x)) ξ|≤δ := by
  obtain ⟨k,hk⟩:=linear_test_refinement B δ hB hδ
  refine ⟨k,fun I J _ _ _ K f Q hf=>?_⟩
  have hμ : SubLaw (unifOn K):=unifOn_sub K
  obtain ⟨r,hr,P,hP⟩:=hk I J (unifOn K) hμ f Q hf
  refine ⟨r,hr,P,fun x=>cashbook_bound _ hμ.nz _ f B hB hf _,fun ξ=>?_⟩
  by_cases hK : pr unif K=0
  · have hz x : ind (K x)=0:=by
      by_contra hh
      have hx : K x:=by by_contra hx; exact hh (ind_zero hx)
      have hm:=weight_le_pr unif_law.nz hx
      rw [hK] at hm
      have hu : 0<unif (α:=Vec I) x:=by rw [unif_apply]; positivity
      linarith
    simp only [hz,mul_zero,linearFourier,avg_zero,abs_zero]
    exact hδ.le
  · have hpos : 0<pr unif K:=lt_of_le_of_ne (pr_nonneg unif_law.nz) (Ne.symm hK)
    have he : linearFourier (fun x=>(f x-banner (unifOn K) (fun x=>(Q x,P*ᵥx)) f x)*ind (K x)) ξ=
        pr unif K*dip (unifOn K) (fun x=>f x-banner (unifOn K) (fun x=>(Q x,P*ᵥx)) f x)
          (vectorPhase ξ) := by
      unfold dip
      rw [←part_reset K _ hpos]
      unfold linearFourier partMean
      apply avg_congr
      intro x _
      ring
    rw [he,abs_mul,abs_of_pos hpos]
    exact (mul_le_mul_of_nonneg_left (hP ξ) hpos.le).trans
      ((mul_le_mul_of_nonneg_right (pr_le_tot unif_law.nz) hδ.le).trans_eq (by rw [unif_law.total,one_mul]))

end
end Lax793645Proofs.Simplifications
