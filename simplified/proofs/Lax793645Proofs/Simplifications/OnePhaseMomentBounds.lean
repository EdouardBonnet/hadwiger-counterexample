import Lax793645Proofs.Simplifications.OnePhaseLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PhaseMomentBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {A : Type} [Fintype A] {p : Shape} {N : ℕ}

def channelPitch (Δ : A→Ambient p N) (read : A→PhasePair p N)
    (w : Wgt A) (S R : Party) :=
  avg (pairW w w) (fun x=>wsign
    (joinPhase p (read x.1) R (Δ x.2)+joinPhase p (read x.2) S (Δ x.1)))

set_option maxHeartbeats 800000 in
/-- The no-cover phase estimate only needs a bound on the channel
marginal. It is independent of how primal frames were constructed. -/
theorem channel_pitch_no_cover (Δ : A→Ambient p N) (read : A→PhasePair p N)
    {w : Wgt A} (hw : IsLaw w) (S R : Party) (hs : S≠0)
    (r m b : ℕ) (hr : ∀ x,epoch p (Δ x)≤r) (hm : 16*r<m) (hb : 1≤b)
    (c ψ H : ℝ) (hc : 0≤c)
    (hh : ∀ t : Cov p N,(∀ i,cdSign p t i≤r*(2^m*(2*b)))→
      pr w (fun i=>covered p t (Δ i))≤c)
    (hψ : 0<ψ) (hH : 0≤H)
    (hcap : ∀ y,mapW w read y≤H*freeH p N y) :
    |channelPitch Δ read w S R|≤ψ+
      bp (2*(r:ℝ)*num (Comp p.g)*N)*(H*(exponentErr p m b c/ψ^(2^m*(2*b)))) := by
  classical
  let g (v : Ambient p N) (x : A):=wsign (joinPhase p (read x) R v)
  have hg v x : |g v x|≤1:=by simp [g]
  let y (v : Ambient p N):=sweep p Δ w (g v) S
  let Q:=exponentErr p m b c/ψ^(2^m*(2*b))
  have h v:=rare_sweep p Δ w (g v) S hw (hg v) hs r m b hr hm hb c ψ hc hh hψ
  let F' (v : Ambient p N) (x : A):=y v (read x)
  let C:={v : Ambient p N//epoch p v≤r}
  let B (x : A):=∃ v : C,ψ≤|F' v.val x|
  have ha (x) : |F' (Δ x) x|≤ψ+ind (B x) := by
    by_cases h : ψ≤|F' (Δ x) x|
    · rw [ind_one (show B x from ⟨⟨Δ x,hr x⟩,h⟩)]
      exact (abs_sweep p Δ w _ S hw (hg _) _).trans (by linarith)
    exact (le_of_not_ge h).trans (le_add_of_nonneg_right (ind_nonneg _))
  have hZ : channelPitch Δ read w S R=avg w (fun x=>F' (Δ x) x) := by
    rw [channelPitch,pairW_avg,avg_avg]
    simp_rw [wsign_add]
    rfl
  rw [hZ]
  refine ((abs_avg_le hw.nz).trans (avg_mono hw.nz ha)).trans ?_
  rw [avg_add,hw.avg_const]
  apply add_le_add_right
  have hz (v : C) : pr w (fun x=>ψ≤|F' v.val x|)≤H*Q := by
    let P (y' : PhasePair p N):=ψ≤|y v.val y'|
    calc
      pr w (fun x=>ψ≤|F' v.val x|)=pr (mapW w read) P := (mapW_pr w read P).symm
      _ ≤ _ := (pr_cap hcap P).trans (mul_le_mul_of_nonneg_left (h _) hH)
  refine (pr_exists_le hw.nz (fun v : C=>fun x=>ψ≤|F' v.val x|)).trans ?_
  refine (Finset.sum_le_sum fun i _=>hz i).trans ?_
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right
  · exact (nbr_eq_card (fun v : Ambient p N=>epoch p v≤r)).symm.trans_le (epoch_count p N r)
  · exact mul_nonneg hH ((pr_nonneg (freeH_law p N).nz).trans (h (0:Ambient p N)))

variable {n : ℕ}

/-- The new one-frame law satisfies the no-cover branch of the phase
alternative, with the same finite moment estimate and a fixed new price. -/
theorem one_pitch_no_cover (Δ : OneUnit p n N→Ambient p (2*N))
    {w : Wgt (OneUnit p n N)} (hw : IsLaw w) (S R : Party) (hs : S≠0)
    (r m b : ℕ) (hr : ∀ x,epoch p (Δ x)≤r) (hm : 16*r<m) (hb : 1≤b)
    (c ψ H : ℝ) (hc : 0≤c)
    (hh : ∀ t : Cov p (2*N),(∀ i,cdSign p t i≤r*(2^m*(2*b)))→
      pr w (fun i=>covered p t (Δ i))≤c)
    (hψ : 0<ψ) (hH : 0≤H) (mix : Mixer p n)
    (hcap : ∀ x,w x≤H*oneUnitRaw mix N x)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4*p.h+3≤N) :
    |channelPitch Δ oneListens w S R|≤ψ+
      bp (2*(r:ℝ)*num (Comp p.g)*(2*N))*(H*oneCubePrice p^2*
        (exponentErr p m b c/ψ^(2^m*(2*b)))) := by
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    channel_pitch_no_cover Δ oneListens hw S R hs r m b hr hm hb c ψ
      (H*oneCubePrice p^2) hc hh hψ (mul_nonneg hH (sq_nonneg _))
      (one_phase_cap hH mix hcap hroom hN)

end
end Lax793645Proofs.Simplifications
