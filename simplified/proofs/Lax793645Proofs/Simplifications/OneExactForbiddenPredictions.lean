import Lax793645Proofs.Simplifications.OneGenericFiniteComparison
import Lax793645Proofs.Simplifications.OneGenericPositiveOptions
import Lax793645Proofs.Simplifications.OneFiniteComparison
import Lax793645Proofs.Simplifications.OneExactPredictionCatalog
import Lax793645Proofs.Simplifications.OneGenericStatusContinuation
import Lax793645Proofs.Simplifications.GenericScalarOptions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample

/-! # Forbidden Predictions -/

noncomputable section
open Filter Matrix Module LinearMap Finset Function
open scoped BigOperators Topology
open Template
open StatusAnalysis
namespace OneExactOptions
open PreparationParameters OneStation PredictionClass Club Guild DualAnalysis
variable {p : Shape} {n N M r s0 K coords : ℕ} {w:OneLeafMixture p n N} {b:PreparationParameters}

def witnessed (w : OneLeafMixture p n N) (v : OneStation p n N K w) (L : OneLoupe w K)
    (m : Mixer p n) (Y : OneSilhouette p N r) (H : Space (OneJointKey p N))
    (B : ℕ) (cat : Nodes→Pulsar p r) (x : OneAspect w) :=
  OnePaletteGood H x.2 ∧ ExactAnnounced (oneWisp p Y)
    (oneWake p Y m x.2 (oneRouteC L v x)) cat B

set_option maxHeartbeats 1000000 in
theorem witnessed_cost (w : OneLeafMixture p n N)
    (v : OneStation p n N (onePreparationPins b) w) (L : OneLoupe w (onePreparationPins b))
    (h : OneShipped w (onePreparationPins b) v L) (m : Mixer p n)
    (Y : OneSilhouette p N r) (H : Space (OneJointKey p N))
    (a : ℝ) (U : Wgt (OneUnit p n N)) (cat : Nodes→Pulsar p r)
    (hp : OneLead U w m b.leafNew (2*b.ζ) (onePreparationPins b)) (ha : 0≤a)
    (hnorm : ∀ x : OneAspect w,OnePaletteGood H x.2→∀ i E,E.card≤b.B→∀ u α f,
      ExactStatusPrediction (oneWisp p Y) (oneWake p Y m x.2 (oneRouteC L v x))
        i E (yokeSet u α) f→
        onePostulates (x.2 i) (oneFromPulse Y f)
          (oneYoke m x.2 i (oneRouteC L v x i u) α) ∅ 0)
    (hYlinear : OneLinearSilhouette Y coords) (hcoords : 8*p.g*coords≤n)
    (hy : ¬oneBoundedLinearPredicts b m w U a) :
    pr (oneTroupe w U) (witnessed w v L m Y H b.B cat)≤0.001 := by
  classical
  let t:=oneTroupe w U
  let F (f : Nodes→Pulsar p r):=fun i=>oneFromPulse Y (f i)
  let P (f : Nodes→Pulsar p r) (x : OneUnit p n N):=∃ u E α,oneGenericSeems b m w x (F f) u E α a
  have ht:=one_troupe_bill hp
  have hf (f : Nodes→Pulsar p r) : pr t (fun x=>P f x.2)≤0.000001 := by
    have he : pr t (fun x=>P f x.2)=pr (w.sap U) (P f) := by rw [←ht.2,mapW_pr]
    rw [he]
    exact le_of_not_ge (fun hmass=>hy
      ⟨F f,⟨coords,hcoords,fun i=>one_linear_from_pulse hYlinear (f i)⟩,hmass⟩)
  have hbound : pr t (fun x=>∃ f∈sevenPredictionPairs cat,P f x.2)≤0.001 := by
    refine ((pr_union_le ht.1.nz (sevenPredictionPairs cat) (fun f x=>P f x.2)).trans
      (Finset.sum_le_sum (fun f _=>hf f))).trans ?_
    rw [sum_const,nsmul_eq_mul]
    have hcard : ((sevenPredictionPairs cat).card:ℝ)≤7:=by
      exact_mod_cast seven_prediction_pairs_card cat
    nlinarith only [hcard]
  refine (pr_on_mono ht.1.nz ?_).trans hbound
  rintro x hx ⟨hgood,f,hfmem,u,α,E,hpred⟩
  have hh:=one_troupe_home hp x hx
  refine ⟨f,hfmem,(fun i=>oneRouteC L v x i (u i)),(fun _=>∅),α,?_,?_⟩
  · intro i
    refine ⟨by simp,?_⟩
    rw [hh.2.1,←(h.charts x.1 i).1]
    exact LinearMap.mem_range_self _ _
  · intro i s hs l
    exact (hnorm x hgood i (E i) (hpred i).1 (u i) (α i) (f i) (hpred i).2 s hs l Flavor.full).trans ha

set_option maxHeartbeats 2000000 in
theorem no_out (w:OneLeafMixture p n N) (b:PreparationParameters)
    (m:Mixer p n) (Y:OneSilhouette p N r) (U:Wgt (OneUnit p n N))
    (v:OneStation p n N (onePreparationPins b) w) (ε η a δ τ:ℝ)
    (h:OneLead U w m b.leafNew (2*b.ζ) (onePreparationPins b)) (ht:v.bank) (he:OneAnalyticParameters p M b s0) (hn:2*p.r≤n)
    (hp:Jubilee p (onePreparationPins b) ε η) (hε:0<ε)
    (hB:oneSupportBudget p (onePreparationPins b) η a)
    (hv:OneGenericBeams m Y w U v a ε δ (1/16))
    (hYlinear:OneLinearSilhouette Y coords) (hcoords:8*p.g*coords≤n)
    (hτ : 0≤τ)
    (H : Space (OneJointKey p N))
    (hgood : pr (w.sap U) (fun o=>¬OnePaletteGood H o)≤1/16)
    (hgap : ∀ o o',OnePaletteGood H o→OnePaletteGood H o'→
      OneFullTableGap Y m (onePreparationPins b) o o')
    (hnorm : ∀ o : OneUnit p n N,OnePaletteGood H o→∀ d : Rates,∀ v : Charts p n d,
      (∀ i z,totalRank (v i z)≤onePreparationPins b)→
      ∀ i E,E.card≤b.B→∀ z α f,
      ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i E (yokeSet z α) f→
        OneTesterFree Y f ∧
        onePostulates (o i) (oneFromPulse Y f) (oneYoke m o i (v i z) α) ∅ 0)
    (hcontinue : ∀ o : OneUnit p n N,OnePaletteGood H o→OneGenericStatusContinues Y m b.B o)
    (hη : η≤bp (-(4*(oneStatusCoordinateBound p ((onePreparationPins b)^2)
      (onePreparationPins b):ℝ)+1)))
    (hsep : TesterSeparated (oneWisp p Y) (OneTesterFree Y))
    (hh:¬oneBoundedLinearPredicts b m w U τ)
    (hu:0.99 < pr (pairW (w.sap U) (w.sap U)) (oneSecureAt w)) :
    False := by
  classical
  let W:=OneAspect w; let K:=(onePreparationPins b); let L:=oneTroupe w U; let V:=oneCirque w U
  let u:=oneWisp p Y
  let β:=trimBeta p K
  let S (x:W):=oneGenericGauze p δ δ Y m K x.2 ∧ OnePaletteGood H x.2
  have hK i: imagePlanRank (w.pin (Subtype.val (show w.T from i))).sp ≤ K :=
    (h.strength.leaf _ i.property).bound
  obtain ⟨g,hg⟩:= one_ready_loupe v ht hK
  let f (x:W):=oneRouteC g v x
  let Q (x:W):=oneWake p Y m x.2 (f x)
  have ht' := he.planted
  have hd (x:W) (hx:S x) : reports p r u (Q x) β δ :=
    one_generic_route_live v g hg m he.planted.hG he.planted.hR hn x Y δ hv.haze.1 (hK x.1) hx.1
  have hL:2*b.B<Fintype.card (Label p.b) := by have hi:=he.spare; omega
  have hβ:=trimBeta_pos p K
  have hrank (x : W) (i : Nodes) (z) : totalRank (f x i z)≤K := by
    apply (one_effective_rank (w.pin x.1.val).sp i _ ?_).trans (hK x.1)
    rw [←(hg.charts x.1 i).1]
    exact LinearMap.mem_range_self _ _
  have hn (x : W) (hx : OnePaletteGood H x.2) :=
    hnorm x.2 hx _ (f x) (hrank x)
  choose d hD hfree using show ∀ x : W,∃ cat : Nodes→Pulsar p r,
      (S x→ExactCatalog u (Q x) b.B cat) ∧ ∀ i,OneTesterFree Y (cat i) from by
    intro x
    by_cases hx : S x
    · obtain ⟨cat,hcat,hfree⟩:=exact_prediction_catalog ht'.hG hv.soft (hd x hx) hβ b.B hL
        (OneTesterFree Y) (one_tester_free_zero Y)
        (fun i E hE z α f hf=>(hn x hx.2 i E hE z α f hf).1)
      exact ⟨cat,fun _=>hcat,hfree⟩
    exact ⟨0,fun h=>(hx h).elim,fun _=>one_tester_free_zero Y⟩
  let X (x:W×W):= oneSecureAt w (x.1.2,x.2.2)
  let Y1 (x:W×W):= witnessed w v g m Y H b.B (d x.2) x.1
  let Y2 (x:W×W):= witnessed w v g m Y H b.B (d x.1) x.2
  let Z (x:W×W):=¬ S x.1∨¬ S x.2
  let P (x:W×W):=v.genericEligiblePair m x.1 x.2 Y a
  have hF:∀ i,V i ≠0 → X i→ ((Z i∨P i)∨ (Y1 i∨Y2 i)) := by
    intro i hi hk
    by_cases hQ:Z i∨P i
    · exact Or.inl hQ
    have ha1:S i.1:=not_not.mp (mt (fun x=>Or.inl (Or.inl x)) hQ)
    have ha2:S i.2:=not_not.mp (mt (fun x=>Or.inl (Or.inr x)) hQ)
    let A : Stalls p := ⊥; let B : Stalls p := ⊥
    let C:= stellar u (Q i.1) (Q i.2) η A B
    have hk0 (i t) := Nat.lt_succ_iff.mp (g.r i t).isLt
    let reserve := oneScalarBudget p K
    have hlabelsA (side) : (A side).card+9*reserve<Fintype.card (Label p.b) := by
      have hreserve := he.reserve
      have hspare := he.spare
      simp only [A,Pi.bot_apply,Finset.bot_eq_empty,card_empty,zero_add]
      change 9*oneScalarBudget p (onePreparationPins b) < _
      omega
    have hlabelsB (side) : (B side).card+9*reserve<Fintype.card (Label p.b) := hlabelsA side
    have hC : richAt C (9*reserve) := plenitude_at_budget (9*reserve)
      hv.soft (hd _ ha1) (hd _ ha2) ht'.hG A B hlabelsA hlabelsB
      hβ hp.pos hp.sturdyR (hk0 _) (hk0 _)
    have hm0:= one_troupe_home h i.1 (left_ne_zero_of_mul hi)
    have hm1:= one_troupe_home h i.2 (right_ne_zero_of_mul hi)
    obtain ⟨k,hk⟩:= v.issueTicket _ _ i.1.1 i.2.1 h.strength.part hm0.1 hm1.1 ht
      (h.strength.leaf _ i.1.1.property).closed (h.strength.leaf _ i.2.1.property).closed hk
    let T:= v.mails i.1.1 i.2.1 k
    let R:= oneHailing (f i.1) (f i.2) T
    have hsupport:= (one_table_gap_dual Y m K i.1.2 i.2.2
      (hgap _ _ ha1.2 ha2.2) (f i.1) (f i.2) (hk0 _) (hk0 _)
      (fun j z=>hrank i.1 j _) (fun j z=>hrank i.2 j _)).mono hη
    have hspan (j : Grid) (S : Straps (Label p.b))
        (hS : ∀ side,(S side).card≤oneScalarBudget p K) :
        (genericStellar u (Q i.1) (Q i.2) η ⊥ ⊥ j).band S=(C j).band ⊥ := by
      apply generic_status_band_stable hv.soft (hd _ ha1) (hd _ ha2) hsupport hp.pos ht'.hG b.B
        (by have hh:=he.spare; omega)
        (hcontinue i.1.2 ha1.2 _ (f i.1)) (hcontinue i.2.2 ha2.2 _ (f i.2)) S ?_ j
      intro side
      have hh:=hS side
      have hh':=he.reserve
      change (S side).card≤oneScalarBudget p (onePreparationPins b) at hh
      omega
    let E : Straps (Label p.b):=⊥
    have hE : sizeB E (8*oneScalarBudget p K):=by intro side; simp [E]
    have hlabels : 9*oneScalarBudget p K<Fintype.card (Label p.b) := by
      simpa only [A,reserve,Pi.bot_apply,Finset.bot_eq_empty,card_empty,zero_add]
        using hlabelsA true
    have hI:=one_generic_scalar_options hv.soft (hd _ ha1) (hd _ ha2)
      ht'.hG ht'.hg (by rw [he.affine]) he.jump hlabels hβ hp.pos hp.sturdyR
      (hk0 _) (hk0 _) hspan (w.pin i.1.1.val) (w.pin i.2.1.val) (hK _) (hK _)
      (f i.1) (f i.2) T (hg.charts _) (hg.charts _) hk.1 hk.2.1
    by_cases hV:scorecard (chapter C E) R
    · obtain ⟨q,g0,F,G,hchance,hstatus,hgeneric⟩ := hI hV
      exact (hQ (Or.inr (v.inform_generic_options m Y i.1 i.2 hm0.2.2.1 hm1.2.2.1
        hm0.2.2.2 hm1.2.2.2 (g.r _) (g.r _) hB hp.pos k hk q g0 F G
        hchance hstatus hgeneric))).elim
    obtain ⟨z,hz1,hz2,hz3⟩ := jargon_score _ _ hV
      (richAt_covers C hC E (fun x => (hE x).trans (by omega)))
    let G0:=outstraps A E true; let G1:=outstraps B E false
    have hu (side j) : (outstraps (⊥ : Stalls p) E side j).card ≤ b.B := by
      simp only [outstraps,Pi.bot_apply,Finset.bot_eq_empty,empty_union]
      have hr := he.reserve
      have hh := hE side
      change _ ≤ 8*oneScalarBudget p (onePreparationPins b) at hh
      omega
    have hE0 (j) : (outstraps A E true j).card < Fintype.card (Label p.b) :=
      (hu true j).trans_lt (by have hs := he.spare; omega)
    have hE1 (j) : (outstraps B E false j).card < Fintype.card (Label p.b) :=
      (hu false j).trans_lt (by have hs := he.spare; omega)
    have hT (j : Grid) := dual_exact_status_predictors hv.soft (hd _ ha1) (hd _ ha2)
      hsupport A B E z hz2 j ht'.hG (hE0 _) (hE1 _)
    right
    have hchoice:=exact_seven_alternative ht'.hG hv.soft (hd _ ha1) (hd _ ha2) hβ b.B
      (by have hs:=he.spare; omega) (OneTesterFree Y) (one_tester_free_zero Y) hsep
      (fun j E hE w α f hf=>(hn i.1 ha1.2 j E hE w α f hf).1)
      (fun j E hE w α f hf=>(hn i.2 ha2.2 j E hE w α f hf).1)
      (d i.1) (d i.2) (hD _ ha1) (hD _ ha2) (hfree _) (hfree _) G0 G1
      (hu true) (hu false) z hz1 hT
    exact hchoice.elim (fun h=>Or.inl ⟨ha1.2,h⟩) (fun h=>Or.inr ⟨ha2.2,h⟩)
  have hL:IsLaw L:= (one_troupe_bill h).1
  have hz0 (i:W): pr L (witnessed w v g m Y H b.B (d i)) ≤ 0.001 :=
    witnessed_cost w v g hg m Y H τ U (d i) h hτ
      (fun x hx j E hE w α f hf=>(hn x hx j E hE w α f hf).2)
      hYlinear hcoords hh
  have hZ1: pr V Y1 ≤ 0.001 := by
    unfold pr V oneCirque; rw [pairW_avg,avg_avg]; exact hL.avg_le hz0
  have hZ2: pr V Y2 ≤0.001 := by unfold pr V oneCirque; rw [pairW_avg]; exact hL.avg_le hz0
  have hO:IsLaw V:=pairW_law hL hL
  have hX :0.99 < pr V X := by rw [←one_cirque_unit h,mapW_pr] at hu; exact hu
  have hP:= show pr V P≤1/16 from hv.zone
  have hbad : pr L (fun x=>¬OnePaletteGood H x.2)≤1/16 := by
    have hb:=hgood
    rw [←(one_troupe_bill h).2,mapW_pr] at hb
    exact hb
  have hsick : pr L (fun x=>¬S x)≤1/8 := by
    have hs : pr L (fun x=>¬S x)=pr L (fun x=>
        ¬oneGenericGauze p δ δ Y m K x.2 ∨ ¬OnePaletteGood H x.2) := by
      congr 1
      funext x
      exact propext not_and_or
    rw [hs]
    exact ((pr_or_le hL.nz).trans (add_le_add (one_generic_sick_bound U v Y h hv).1 hbad)).trans
      (by norm_num)
  have hZ : pr V Z≤1/8+1/8 := by
    apply (pr_or_le hO.nz).trans
    refine add_le_add ?_ ?_
    · have heq:=pairW_pr L L (fun x=>¬S x) (fun _=>True)
      have hh : pr V (fun x=>¬S x.1)=pr L (fun x=>¬S x) := by
        simpa only [V,oneCirque,L,pr_true,hL.total,mul_one,and_true] using heq
      exact hh.trans_le hsick
    · have heq:=pairW_pr L L (fun _=>True) (fun x=>¬S x)
      have hh : pr V (fun x=>¬S x.2)=pr L (fun x=>¬S x) := by
        simpa only [V,oneCirque,L,pr_true,hL.total,one_mul,true_and] using heq
      exact hh.trans_le hsick
  have hx: pr V X≤(1/8+1/8+1/16)+(0.001+0.001):=
    ((pr_on_mono hO.nz hF).trans (pr_or_le hO.nz)).trans
      (add_le_add ((pr_or_le hO.nz).trans (add_le_add hZ hP)) ((pr_or_le hO.nz).trans
        (add_le_add hZ1 hZ2)))
  linarith only [hX,hx]
end OneExactOptions

end

end Lax793645Proofs.Simplifications
