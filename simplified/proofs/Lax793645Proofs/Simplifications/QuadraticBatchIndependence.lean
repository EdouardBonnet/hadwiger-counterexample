import Lax793645Proofs.Simplifications.QuadraticLaneLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G H : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype H]
  [DecidableEq I] [DecidableEq J] [DecidableEq G] {N : ℕ}
variable {g : Route (I×J) G}

private def condMean (p : H→Prop) (f : Wgt H) :=
  avg unif (fun x => ind (p x)*f x)
private theorem cond_reset [Nonempty H] (p : H→Prop) (f : Wgt H) (h : 0<pr unif p) :
    condMean p f=pr unif p * avg (unifOn p) f := by
  rw [←on_unif]; unfold onW
  rw [avg_norm,subW_tot]
  have he : condMean p f = avg (subW unif p) f := by simp only [avg,subW,mul_assoc]; rfl
  rw [he]
  field_simp

set_option maxHeartbeats 800000 in
theorem quadratic_lane_means (Z : GeoM g) (f : I → Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (k : ℝ) (hk : ∀ i,num (Port g i)≤k) :
    |condMean (quadraticFramePart Z) (brightProd f) - bp (-quadraticReferenceCost (crossroads g)) *
      ∏ i,condMean (quadraticFramePart (laneM Z i)) (f i)|≤twinkle g k N := by
  classical
  let E := crossroads g
  let F i (x : Rack J N) := ind (quadraticFramePart (laneM Z i) x)*f i x
  have hF i x : |F i x|≤1 := by
    unfold F; by_cases h : quadraticFramePart (laneM Z i) x <;> simp only [h,ind_true,ind_false,one_mul,
      zero_mul]; exact hf i x; norm_num
  have hE i (h : i∈E) : i.1.1≠i.2.1 := fun he =>
    (mem_sdiff.mp h).2 (mem_filter.mpr ⟨(mem_sdiff.mp h).1,he⟩)
  have ht := quadratic_cross_expand F hF E (geoMatrix g Z) hE
  have hP : avg unif (brightProd F)=∏ i, condMean (quadraticFramePart (laneM Z i)) (f i) :=
    (led_uniform (prodW F)).trans (prodW_avg _ _)
  let A x := ind (quadraticTraced E (geoMatrix g Z) ((rackCoordinates (I×J) N).symm x))*brightProd F x
  have hA x : |A x|≤1 := by
    by_cases h : quadraticTraced E (geoMatrix g Z) ((rackCoordinates (I×J) N).symm x)
    · unfold A; rw [ind_one h,one_mul]; exact lane_abs F hF _ x
    unfold A; rw [ind_zero h,zero_mul]; norm_num
  have hi x :
      ind (quadraticFramePart Z x) * brightProd f x= ind (quadraticInjPart g x) * A x := by
    rw [quadratic_frame_road g]; unfold A F
    simp only [ind_and, ind_all,brightProd,Finset.prod_mul_distrib]
    ring
  have hg :
      |condMean (quadraticFramePart Z) (brightProd f) - avg unif A|≤ num G*(2*bp (k-N)) := by
    unfold condMean
    simp_rw [hi]
    rw [← avg_sub]
    refine (abs_avg_le unif_law.nz).trans ((avg_mono unif_law.nz (g:=fun x =>
      ind (¬quadraticInjPart g x)) fun i => ?_).trans (quadratic_inj_failure g k hk))
    by_cases h : quadraticInjPart g i <;>
      simp only [h,ind_true,not_true,ind_false,one_mul,sub_self,abs_zero,zero_mul,zero_sub,
        abs_neg,not_false_eq_true]; exact le_rfl; exact hA _
  rw [hP] at ht
  unfold twinkle
  apply le_trans _ (add_le_add hg ht)
  exact abs_sub_le ..

omit [DecidableEq I] in
theorem quadratic_lane_norm (Z : GeoM g) (hN : ∀ i, 2*num (Port g i)+2≤ (N:ℝ))
    (i : I) : 0<pr unif (quadraticFramePart (laneM Z i) (N:=N)) := by
  have he j : Injective (condLane g i j) := by intro a b h; exact Subtype.ext (congrArg
    (fun x : Port g j => x.val.2) h)
  have hx j : num (Port (street g i) j)≤num (Port g j) := by
    exact_mod_cast Fintype.card_le_of_injective _ (he j)
  refine lt_of_lt_of_le (inv_pos_of_pos (quadratic_net_fact_pos _)) (quadratic_net_norm _ (laneM Z i) (fun j => ?_))
  linarith only [hx j,hN j]

set_option maxHeartbeats 800000 in
theorem quadratic_compare_lanes (Z : GeoM g) (f : I→ Wgt (Rack J N)) (hf : ∀ i x,|f i x|≤1)
    (k : ℝ) (hk : ∀ i,num (Port g i)≤k) (hN : ∀ i,2*num (Port g i)+2≤ (N:ℝ)) :
    |avg (quadraticStation Z N) (brightProd f)- ∏ i,avg (quadraticStation (laneM Z i) N) (f i)|≤
      2*quadraticNetFact g*twinkle g k N := by
  classical
  let A := pr unif (quadraticFramePart (N:=N) Z)
  let B i := pr unif (quadraticFramePart (N:=N) (laneM Z i))
  let u := avg (quadraticStation Z N) (brightProd f)
  let v i := avg (quadraticStation (laneM Z i) N) (f i)
  let P := bp (-quadraticReferenceCost (crossroads g))*(∏ i, B i)
  let V := ∏ i,v i
  have hV : |V|≤1 := by
    unfold V
    rw [Finset.abs_prod]
    have he (i) :
        SubLaw (quadraticStation (laneM Z i) N) := unifOn_sub _
    refine (Finset.prod_le_prod (fun i _ => abs_nonneg _)
      (fun i _ => (abs_avg_le (he i).nz).trans ((he i).avg_le zero_le_one (hf i)))).trans_eq ?_
    simp
  have hh := quadratic_net_norm g Z hN
  have h0 : 0<A := (inv_pos_of_pos (quadratic_net_fact_pos _)).trans_le hh
  have h1 : |A*u-P*V|≤twinkle g k N := by
    have hb := quadratic_lane_norm (N:=N) Z hN
    have ht := quadratic_lane_means Z f hf k hk
    rw [cond_reset (quadraticFramePart (N:=N) Z) _ h0] at ht
    simp_rw [cond_reset _ _ (hb _)] at ht; rw [Finset.prod_mul_distrib] at ht
    simpa only [A,B,u,v,P,V,quadraticStation,mul_assoc] using ht
  have h2 : |A-P|≤ twinkle g k N := by
    let F (i:I) := fun _ : Rack J N => (1:ℝ)
    have ht := quadratic_lane_means Z F (by intro i x; simp [F]) k hk
    have he (i : I) :
        condMean (quadraticFramePart (laneM Z i)) (F i)=B i := by simp only [F,condMean,mul_one]; rfl
    have hx :
        condMean (quadraticFramePart (N:=N) Z) (brightProd F)=A := by
      simp only [F,brightProd,condMean,Finset.prod_const_one,mul_one,A,pr]
    simp_rw [he,hx] at ht; exact ht
  have hg : A * |u-V|≤2*twinkle g k N := by
    have hh : |(A-P)*V|≤twinkle g k N := by
      rw [abs_mul]; exact ((mul_le_mul_of_nonneg_left hV (abs_nonneg _)).trans_eq (mul_one _)).trans h2
    calc A*|u-V|= |(A*u-P*V)-(A-P)*V| := by
                 rw [show A*u-P*V-(A-P)*V=(A*(u-V)) by ring,abs_mul,abs_of_nonneg h0.le]
         _ ≤ _ := ((abs_sub ..).trans (add_le_add h1 hh)).trans_eq (two_mul _).symm
  apply le_of_mul_le_mul_left _ (inv_pos_of_pos (quadratic_net_fact_pos g))
  exact ((mul_le_mul_of_nonneg_right hh (abs_nonneg _)).trans hg).trans_eq (by
    have h := quadratic_net_fact_pos g
    field_simp)

end
end Lax793645Proofs.Simplifications
