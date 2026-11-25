import Lax793645Proofs.Simplifications.FourierNorm
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ConditionalProjection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Bounded tests have a bounded linear partition with uniformly small
Fourier residual. The probability law may be a prescribed Gram law. -/
theorem linear_test_partition (B δ : ℝ) (hB : 0≤B) (hδ : 0<δ) :
    ∃ k : ℕ,∀ (I : Type) [Fintype I] [DecidableEq I]
      (μ : Wgt (Vec I)),SubLaw μ → ∀ f : Wgt (Vec I),(∀ x,|f x|≤B) →
      ∃ r : ℕ,r≤k ∧ ∃ P : Mat (Fin r) I,
        ∀ ξ : Vec I,|dip μ (fun x=>f x-banner μ P.mulVec f x) (vectorPhase ξ)|≤δ := by
  classical
  obtain ⟨k,hk⟩:=exists_nat_gt (B^2/δ^2)
  rw [div_lt_iff₀ (sq_pos_of_pos hδ)] at hk
  refine ⟨k,fun I _ _ μ hμ f hf=>?_⟩
  by_contra! h
  have he (r : ℕ) (hr : r≤k) : ∃ P : Mat (Fin r) I,
      (r:ℝ)*δ^2≤ode μ (banner μ P.mulVec f) := by
    induction r with
    | zero =>
      refine ⟨0,?_⟩
      simp only [Nat.cast_zero,zero_mul]
      exact ode_nonneg hμ.nz _
    | succ r ih =>
      obtain ⟨P,hP⟩:=ih (by omega)
      obtain ⟨ξ,hξ⟩:=h r (by omega) P
      let R : Mat (Fin (r+1)) I:=Fin.cons ξ P
      let Q (x : Vec (Fin (r+1))) : Vec (Fin r):=fun i=>x i.succ
      let w (x : Vec (Fin (r+1))) : ℝ:=wsign (x 0)
      have hQ : Q∘R.mulVec=P.mulVec:=by
        funext x i
        rfl
      have hw : w∘R.mulVec=vectorPhase ξ:=rfl
      have hgain:=archive_gain hμ f R.mulVec Q w (fun x=>by dsimp [w]; exact (wsign_abs _).le)
      rw [hQ,hw] at hgain
      have hsq := sq_le_sq₀ hδ.le (abs_nonneg _) |>.mpr hξ.le
      rw [sq_abs] at hsq
      refine ⟨R,?_⟩
      push_cast
      linarith only [hP,hgain,hsq]
  obtain ⟨P,hP⟩:=he k le_rfl
  have hb x : |banner μ P.mulVec f x|≤B:=
    cashbook_bound μ hμ.nz P.mulVec f B hB hf (P.mulVec x)
  exact (not_lt_of_ge (hP.trans (ode_upper hμ _ B hb))) hk

end
end Lax793645Proofs.Simplifications
