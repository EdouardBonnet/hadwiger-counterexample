import Lax793645Proofs.Simplifications.QuadraticPhaseActionLaws
import Lax793645Proofs.Simplifications.OneChannelImageBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

def channelRowsPairEquiv (p : Shape) (N : ℕ) :
    Mat (HyperbolicIdx p.h) (Fin (2*N))≃ₗ[F]HFrame p (2*N) :=
  (Matrix.transposeLinearEquiv _ _ F F).trans splitChannelMatrix

theorem channel_rows_pair_uniform : mapW unif (channelRowsPairEquiv p N)=pairW unif unif := by
  rw [←pair_unif]
  exact unif_equiv (channelRowsPairEquiv p N).toEquiv

theorem channel_rows_pair_value (T : OneFrame p n N) :
    channelRowsPairEquiv p N (oneChannelRows T)=oneChannelPairEquiv p N (oneChannels T) := by
  change splitChannelMatrix ((splitChannelMatrix.symm (oneChannelPairEquiv p N (oneChannels T)))ᵀᵀ)=_
  rw [Matrix.transpose_transpose,LinearEquiv.apply_symm_apply]

theorem one_unit_phase_channel_cap {w : Wgt (OneUnit p n N)} {C : ℝ}
    (hC : 0≤C) (m : Mixer p n) (i : Bool)
    (hcap : ∀ o,mapW w (fun x=>x i) o≤C*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N)
    (e : Comp p.g) (P : HFrame p (2*N)) :
    mapW w (fun x=>onePhaseCube (x i) e) P≤C*oneChannelPrice p*pairW unif unif P := by
  have hh:=mapW_cap (one_unit_channel_rows_cap hC m i hcap hroom hN e)
    (channelRowsPairEquiv p N) P
  rw [mapW_nested,channel_rows_pair_uniform] at hh
  have he : (channelRowsPairEquiv p N)∘(fun x : OneUnit p n N=>oneChannelRows (x i e))=
      (fun x=>onePhaseCube (x i) e) := funext (fun x=>channel_rows_pair_value (x i e))
  rw [he] at hh
  exact hh

/-- The quadratic polar-action point estimate for the actual frame law.
Any additional acceptance or diagonal-status checks can be intersected
with this event without increasing its unnormalized probability. -/
theorem one_phase_action_bound {w : Wgt (OneUnit p n N)} {C : ℝ}
    (hC : 0≤C) (m : Mixer p n) (i : Bool)
    (hcap : ∀ o,mapW w (fun x=>x i) o≤C*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N)
    (e : Comp p.g) {d : ℕ} (T : Mat (Fin (2*N)) (Fin d))
    (B : Mat (Fin (2*N)) (Fin p.h)→Mat (Fin (2*N)) (Fin d)) :
    pr w (fun o=>Function.Injective ((onePhaseCube (o i) e).1ᵀ*T).mulVec ∧
      quadraticPhaseAction (onePhaseCube (o i) e).1 T (onePhaseCube (o i) e).2=
        B (onePhaseCube (o i) e).1)≤
      C*oneChannelPrice p*bp (-((2*(N:ℝ)-p.h)*d)) := by
  have hh:=quadratic_phase_read_cap w (fun o=>onePhaseCube (o i) e)
    (mul_nonneg hC (bp_pos _).le) (one_unit_phase_channel_cap hC m i hcap hroom hN e) T B
  convert hh using 1 <;> simp [num,oneChannelPrice]

end
end Lax793645Proofs.Simplifications
