import Lax793645Proofs.Simplifications.QuadraticReferenceComparison
import Lax793645Proofs.Simplifications.QuadraticBatchIndependence

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
  [DecidableEq I] [DecidableEq J] [DecidableEq G] {N : ℕ}
variable {g : Route (I×J) G}

theorem quadratic_wave_road (Z : GeoM g) (x : Rack (I×J) N) :
    quadraticWavePart Z x ↔
      quadraticTraced (crossroads g) (geoMatrix g Z) ((rackCoordinates (I×J) N).symm x) ∧
      ∀ i,quadraticWavePart (laneM Z i) (led i x) := by
  have hl i : (geoMatrix g Z).submatrix (Prod.mk i) (Prod.mk i)=
      geoMatrix (street g i) (laneM Z i) := by
    ext u v
    by_cases he : g (i,u)=g (i,v)
    · simp only [geoMatrix,submatrix_apply,street,dif_pos he,laneM,condLane]
    · simp only [geoMatrix,submatrix_apply,street,dif_neg he]
  simp only [quadraticWavePart,quadratic_lane_road,hl]

theorem quadratic_wave_means (Z : GeoM g) (f : I → Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1) :
    |partMean (quadraticWavePart Z) (brightProd f) - bp (-quadraticReferenceCost (crossroads g)) *
      ∏ i,partMean (quadraticWavePart (laneM Z i)) (f i)|≤bp (-(N:ℝ)/2) := by
  classical
  let E := crossroads g
  let F i (x : Rack J N) := ind (quadraticWavePart (laneM Z i) x)*f i x
  have hF i x : |F i x|≤1 := by
    unfold F; by_cases h : quadraticWavePart (laneM Z i) x <;> simp only [h,ind_true,ind_false,one_mul,
      zero_mul]; exact hf i x; norm_num
  have hE i (h : i∈E) : i.1.1≠i.2.1 := fun he =>
    (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1,he⟩)
  have ht := quadratic_cross_expand F hF E (geoMatrix g Z) hE
  have hP : avg unif (brightProd F)=∏ i, partMean (quadraticWavePart (laneM Z i)) (f i) :=
    (led_uniform (prodW F)).trans (prodW_avg _ _)
  let A x := ind (quadraticTraced E (geoMatrix g Z) ((rackCoordinates (I×J) N).symm x))*brightProd F x
  have hi x :
      ind (quadraticWavePart Z x) * brightProd f x= A x := by
    rw [quadratic_wave_road]; unfold A F E
    simp only [ind_and, ind_all,brightProd,Finset.prod_mul_distrib]
    ring
  rw [hP] at ht
  change |avg unif _-_ *∏ i,partMean _ _|≤_
  simp_rw [hi]
  exact ht


theorem quadratic_wave_lane_norm (Z : GeoM g) (hN : ∀ i,2*num (Port g i)+2≤(N:ℝ))
    (i : I) : 0<pr unif (quadraticWavePart (laneM Z i) (N:=N)) :=
  (quadratic_lane_norm Z hN i).trans_le
    (pr_mono unif_law.nz (fun x hx=>((quadratic_frame_test _ _ x).mp hx).1))

set_option maxHeartbeats 800000 in
theorem quadratic_compare_waves (Z : GeoM g) (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (hN : ∀ i,2*num (Port g i)+2≤(N:ℝ)) :
    |avg (quadraticWave Z N) (brightProd f)- ∏ i,avg (quadraticWave (laneM Z i) N) (f i)|≤
      2*quadraticNetFact g*bp (-(N:ℝ)/2) := by
  classical
  let A := pr unif (quadraticWavePart (N:=N) Z)
  let B i := pr unif (quadraticWavePart (N:=N) (laneM Z i))
  let u := avg (quadraticWave Z N) (brightProd f)
  let v i := avg (quadraticWave (laneM Z i) N) (f i)
  let P := bp (-quadraticReferenceCost (crossroads g))*(∏ i, B i)
  let V := ∏ i,v i
  have hV : |V|≤1 := by
    unfold V
    rw [Finset.abs_prod]
    have he (i) :
        SubLaw (quadraticWave (laneM Z i) N) := unifOn_sub _
    refine (Finset.prod_le_prod (fun i _ => abs_nonneg _)
      (fun i _ => (abs_avg_le (he i).nz).trans ((he i).avg_le zero_le_one (hf i)))).trans_eq ?_
    simp
  have hh := quadratic_wave_norm g Z hN
  have h0 : 0<A := (inv_pos_of_pos (quadratic_net_fact_pos g)).trans_le hh
  let e := bp (-(N:ℝ)/2)
  have h1 : |A*u-P*V|≤e := by
    have hb := quadratic_wave_lane_norm (N:=N) Z hN
    have ht := quadratic_wave_means Z f hf
    rw [part_reset (quadraticWavePart (N:=N) Z) _ h0] at ht
    simp_rw [part_reset _ _ (hb _)] at ht; rw [Finset.prod_mul_distrib] at ht
    simpa only [A,B,u,v,P,V,quadraticWave,mul_assoc] using ht
  have h2 : |A-P|≤ e := by
    let F (i:I) := fun _ : Rack J N => (1:ℝ)
    have ht := quadratic_wave_means Z F (by intro i x; simp [F])
    have he (i : I) :
        partMean (quadraticWavePart (laneM Z i)) (F i)=B i := by simp only [F,partMean,mul_one]; rfl
    have hx :
        partMean (quadraticWavePart (N:=N) Z) (brightProd F)=A := by
      simp only [F,brightProd,partMean,Finset.prod_const_one,mul_one,A,pr]
    simp_rw [he,hx] at ht; exact ht
  exact lane_collapse A P u V e _ (quadratic_net_fact_pos g) hh hV h1 h2

end
end Lax793645Proofs.Simplifications
