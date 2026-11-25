import Lax793645Proofs.Simplifications.QuadraticLaneLaws
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.GramConditionedLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
  [DecidableEq I] [DecidableEq J] [DecidableEq G] {N : ℕ}

def quadraticWavePart {g : Route I G} (Q : GeoM g) (x : Rack I N):=
  quadraticTraced (crowded g) (geoMatrix g Q) ((rackCoordinates I N).symm x)

def quadraticWave {g : Route I G} (Q : GeoM g) (N : ℕ) : Wgt (Rack I N):=
  unifOn (quadraticWavePart Q)

theorem quadratic_wave_norm (g : Route I G) (Q : GeoM g)
    (hN : ∀ i,2*num (Port g i)+2≤N) :
    (quadraticNetFact g)⁻¹≤pr unif (quadraticWavePart (N:=N) Q) :=
  (quadratic_net_norm g Q hN).trans
    (pr_mono unif_law.nz (fun x hx=>(quadratic_frame_test g Q x).mp hx |>.1))

set_option maxHeartbeats 500000 in
theorem quadratic_compare_station {g : Route J G} (Z : GeoM g) (f : Wgt (Rack J N))
    (hf : ∀ x,|f x|≤1) (k : ℝ) (hk : ∀ i,num (Port g i)≤ k)
    (hN : 2*k+2≤(N:ℝ)) :
    |avg (quadraticStation Z N) f- avg (quadraticWave Z N) f| ≤
      2 * quadraticNetFact g * (num G*(2*bp (k-N))) := by
  classical
  have hh i : 2*num (Port g i)+2≤(N:ℝ) := by linarith only [hk i,hN]
  let A := pr unif (quadraticFramePart Z (N:=N))
  let B := pr unif (quadraticWavePart Z (N:=N))
  let Q := avg (quadraticWave Z N) f
  let W := avg (quadraticStation Z N) f
  let e := num G*(2*bp (k-N))
  have he (f : Wgt (Rack J N)) (hf : ∀ x,|f x|≤1) :
      |partMean (quadraticFramePart Z) f-partMean (quadraticWavePart Z) f|≤ e := by
    unfold partMean
    rw [←avg_sub]
    have hi (x : Rack J N) :
        |ind (quadraticFramePart Z x)*f x-ind (quadraticWavePart Z x)*f x| ≤ ind (¬quadraticInjPart g x) := by
      rw [quadratic_frame_test]
      change |ind (quadraticWavePart Z x ∧ quadraticInjPart g x)*f x-
        ind (quadraticWavePart Z x)*f x|≤_
      by_cases h : quadraticInjPart g x
      · simp only [h,and_true,not_true,ind_false,sub_self,abs_zero,le_refl]
      by_cases h' : quadraticWavePart Z x
      · simpa [h,h',ind] using hf x
      simp [h,h',ind]
    exact (abs_avg_le unif_law.nz).trans
      ((avg_mono unif_law.nz hi).trans (quadratic_inj_failure g k hk))
  have hx := quadratic_net_norm g Z hh
  have hA : 0<A := (inv_pos_of_pos (quadratic_net_fact_pos g)).trans_le hx
  have hB : 0<B := (inv_pos_of_pos (quadratic_net_fact_pos g)).trans_le (quadratic_wave_norm g Z hh)
  have h1 := he f hf
  rw [part_reset (quadraticFramePart Z) f hA,part_reset (quadraticWavePart Z) f hB] at h1
  have h2 : |A-B|≤e := by
    have ht := he (fun i => 1) (by intro i; norm_num)
    simp only [partMean,mul_one] at ht
    exact ht
  have h := unifOn_sub (quadraticWavePart Z (N:=N))
  exact lane_collapse A B W Q e _ (quadratic_net_fact_pos g) hx
    ((abs_avg_le h.nz).trans (h.avg_le zero_le_one hf)) h1 h2
end
end Lax793645Proofs.Simplifications
