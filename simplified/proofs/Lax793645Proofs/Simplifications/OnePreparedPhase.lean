import Lax793645Proofs.Simplifications.OnePreparedTrimming
import Lax793645Proofs.Simplifications.OnePredictionClassification

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M}
  {P Q : OneCampaign p M}

theorem OneDosed.citable (h : OneDosed q l m w s b P) (hl : l≤atTop) (hM : 1≤M) :
    OneCitable q l p M m w s b P :=
  ⟨(warm.const (one_trend_sizes l hl hM).2 pollen_pos).mono h.lower,h.forecast,
    h.mark.mono (fun n hn _ _ x _ hx=>hn x hx),pollen,pollen_pos,h.lower⟩

theorem OneDosed.stake (h : OneDosed q l m w s b P) (hl : l≤atTop)
    (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n)) :
    ∀ᶠ n in l,let N:=M*n;let v:=onePotion s w P n;
      IsLaw v ∧ oneBySide v (m n) q.spear ∧
        ∀ x,v x≤bp (q.spJoint*(2*N))*oneUnitRaw (m n) N x := by
  filter_upwards [hx,hw,h.lower,(h.citable hl hq.hM).on_law hl hq hw hx,
    (one_trend_sizes l hl hq.hM).2.eventually (eventually_ge_atTop 100)]
    with n hs hn hP hv hN
  have hc (x) : onePotion s w P n x≤bp 100*w n x:=one_potency hn.law hs.weight (P n) hP x
  refine ⟨hv,one_upper_side hn.border hc (bp_pos _).le le_rfl,fun x=>?_⟩
  apply (hc x).trans
  apply (mul_le_mul_of_nonneg_left (hn.total x) (bp_pos _).le).trans
  rw [←mul_assoc,←bp_add]
  apply mul_le_mul_of_nonneg_right (bp_le ?_) (prodW_nonneg (fun _=>one_raw_nonneg (m n)) x)
  unfold spJoint
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hN ⊢
  linarith only [hN]

theorem one_citable_interpose
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P)
    (h : warm l (fun n=>((2*(M*n):ℕ):ℝ)) (fun n=>pr (onePotion s w P n) (Q n)))
    (hret : ∃ c : ℝ,0<c ∧ ∀ᶠ n in l,c≤pr (onePotion s w P n) (Q n)) :
    let Y:=fun n x=>P n x ∧ Q n x;
    OneCitable q l p M m w s b Y ∧
      ∀ᶠ n in l,onePotion s w Y n=onW (onePotion s w P n) (Q n) := by
  let Y : OneCampaign p M:=fun n x=>P n x ∧ Q n x
  have hz : ∀ᶠ n in l,IsLaw ((s n).sap (w n)) := by
    filter_upwards [hw,hx] with n hn hs
    exact ImageLeafMixture.sap_law (lt_of_lt_of_le (by norm_num) hs.weight) hn.law
  obtain ⟨a,ha,hA⟩:=hb.retained
  obtain ⟨c,hc,hC⟩:=hret
  have hproduct : ∀ᶠ n in l,a*c≤pr ((s n).sap (w n)) (Y n) := by
    filter_upwards [hz,hA,hC] with n hn hA hC
    exact (mul_le_mul hA hC hc.le (ha.trans_le hA).le).trans_eq (pr_of_on hn.nz (P n) (Q n)).symm
  have hm : OneCitable q l p M m w s b Y := by
    refine ⟨(hb.mass.mul h).mono ?_,hb.forecast,
      hb.mark.mono (fun n hn i hi x hx hp=>hn i hi x hx hp.1),a*c,mul_pos ha hc,hproduct⟩
    filter_upwards [hz] with n hn
    exact (pr_of_on hn.nz (P n) (Q n)).symm.le
  refine ⟨hm,?_⟩
  filter_upwards [hz,hb.mass.positive,h.positive] with n hn ht he
  exact (on_both ((s n).sap (w n)) (P n) (Q n) hn.nz ht he).symm

theorem one_epic_bounds {p : Shape} {n N : ℕ} (x : OneUnit p n N)
    (z : Bool→Profile p n) (h : ∀ i,totalRank (z i)≤q.e) :
    epoch p (oneMarkedDelta x z)≤q.rank := by
  have hh : epoch p (oneMarkedDelta x z)≤
      epoch p (oneImageProfile (x true) (z true))+
        epoch p (oneImageProfile (x false) (z false)) := by
    unfold epoch
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun e _=>mrk_add_le _ _
  exact hh.trans ((add_le_add ((one_image_profile_rank _ _).trans (h true))
    ((one_image_profile_rank _ _).trans (h false))).trans (by unfold rank; omega))

set_option maxHeartbeats 900000 in
/-- Classification now reaches the actual one-frame phase alternative;
the retained phase event is charged before normalizing the next law. -/
theorem one_phase_split (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneDosed q l m w s b P)
    (he : ∀ᶠ n in l,∀ x,P n x → oneMarkedDelta x (b.m n x)≠0) :
    ∃ R : OneCampaign p M,OneCitable q l p M m w s b R ∧ ∀ᶠ n in l,
      let v:=onePotion s w R n;
      oneTonalMix (fun x=>oneMarkedDelta x (b.m n x)) v ∨
        oneTonalTiny (fun x=>oneMarkedDelta x (b.m n x)) v q.d := by
  classical
  let c:=(tinyPhase p.g q.rank q.spJoint/2)*(coin/2)
  have hc : 0<c:=mul_pos (half_pos (tinyPhase_pos ..)) (by norm_num [coin])
  let v:=onePotion s w P
  let R n (A : OneUnit p n (M*n)→Prop):=
    c≤pr (v n) A ∧ (oneTonalMix (fun x=>oneMarkedDelta x (b.m n x)) (onW (v n) A) ∨
      oneTonalTiny (fun x=>oneMarkedDelta x (b.m n x)) (onW (v n) A) q.d)
  obtain ⟨A,hA⟩ : ∃ A : OneCampaign p M,∀ᶠ n in l,R n (A n) := by
    refine taking ?_
    filter_upwards [hb.stake hl hq hw hx,hq.wrap.filter_mono hl,he,hb.capped,hb.mark]
      with n hn ht he hr hm
    change ∃ _,c≤_ ∧ _
    apply one_phase_alternative (b.m n) (m n) (ht.2.2.2.2.1 _) hn.1 hn.2.1 hn.2.2
    · intro x hx i
      exact ((one_effective_mem _ _ _).mp (((hm x (onW_ne hx).1).1.1 i).2)).1
    · intro x hx
      exact ⟨he x (onW_ne hx).1,(hr x true).trans (by unfold rank; omega)⟩
    exact fun x=>one_epic_bounds x (b.m n x) (hr x)
  have hmass : warm l (fun n=>((2*(M*n):ℕ):ℝ)) (fun n=>pr (v n) (A n)):=
    (warm.const (one_trend_sizes l hl hq.hM).2 hc).mono (hA.mono fun n hn=>hn.1)
  obtain ⟨h1,h2⟩:=one_citable_interpose hw hx (hb.citable hl hq.hM) hmass ⟨c,hc,hA.mono (fun _ h=>h.1)⟩
  refine ⟨_,h1,?_⟩
  filter_upwards [h2,hA] with n hn ht
  dsimp only
  rw [hn]
  exact ht.2

end
end Lax793645Proofs.Simplifications
