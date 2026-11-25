import Lax793645Proofs.Simplifications.ConstantRetention
/- Closed-pin population restriction, adapted from the vendored
Apache-2.0 PreparedPopulationTrimming finite conditioning proof. -/
import Lax793645Proofs.Simplifications.OnePreparationBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M}

theorem one_trend_sizes (l : Filter ℕ) (hl : l≤atTop) {M : ℕ} (hM : 1≤M) :
    Tendsto (fun n : ℕ=>2*(M*n)) l atTop ∧
      Tendsto (fun n : ℕ=>((2*(M*n):ℕ):ℝ)) l atTop := by
  simpa only [Nat.mul_assoc] using trend_sizes l hl (M:=2*M) (by omega)

theorem one_retain_initial (hl : l≤atTop) (hq : OnePlanted q p M)
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n)) :
    OneDurable q l m w s := by
  refine ⟨((warm.const (one_trend_sizes l hl hq.hM).2 (by norm_num : 0<(1/2:ℝ))).mono
    (hx.mono fun i hi=> hi.weight)),?_,1/2,by norm_num,hx.mono (fun i hi=>hi.weight)⟩
  filter_upwards [hx] with n hn
  have hh := hq.early
  refine ⟨image_strength_slide hn.strength ?_ ?_ ?_ (prodW_nonneg (fun _=>one_raw_nonneg (m n))),
    fun i hi x hx => (hn.onTile i hi x hx).2.2⟩
  · unfold leafNew; linarith [(Nat.cast_nonneg q.u : 0≤(q.u:ℝ)),(Nat.cast_nonneg q.s :
      0≤(q.s:ℝ))]
  · linarith only [hh.pos]
  unfold onePreparationPins; omega

variable {P : OneCampaign p M}
structure OneCitable (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : OneTale p M) (s : OneRhythms p M) (b : OneSketch p M) (P : OneCampaign p M) : Prop where
  mass : warm l (fun i=> ((2*(M*i):ℕ):ℝ)) (fun i=>pr ((s i).sap (w i)) (P i))
  forecast : OneLedger b l
  mark : ∀ᶠ i in l, (s i).within (fun x => P i x → oneEngrave b q m s i x)
  retained : ∃ c : ℝ,0<c ∧ ∀ᶠ n in l,c≤pr ((s n).sap (w n)) (P n)

def onePotion (s : OneRhythms p M) (w : OneTale p M) (P : OneCampaign p M) : OneTale p M :=
  fun n => onW ((s n).sap (w n)) (P n)
def oneCharm (s : OneRhythms p M) (w : OneTale p M) (P : OneCampaign p M) (b : OneSketch p M) :=
  fun n => pr (pairW (onePotion s w P n) (onePotion s w P n)) (oneMatchProg b n)

theorem OneCitable.on_law (h : OneCitable q l p M m w s b P)
    (hl : l ≤ atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n)) :
    ∀ᶠ n in l, IsLaw (onePotion s w P n) := by
  filter_upwards [h.mass.positive,hw,(one_retain_initial hl hq hx).mass.positive] with n hn ht hv
  exact Lax793645Proofs.Upstream.OAI.HadwigerCounterexample.on_law (ImageLeafMixture.sap_law hv ht.law).nz hn

set_option maxHeartbeats 1400000 in
theorem one_drop_harvest (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P) :
    ∃ t : OneRhythms p M, OneDurable q l m w t ∧
      OneBright q l m t b ∧
      (∀ᶠ n in l,(t n).within (fun x=>inTiles (s n).T x∧P n x)) ∧
      ∃ d,ExpSmall l (fun n=> ((2*(M*n):ℕ):ℝ)) d ∧
        ∀ᶠ n in l,oneCharm s w P b n-d n ≤ oneGlow t w b n := by
  classical
  let N (n:ℕ) := M*n; let z (n:ℕ):ℝ:=(2*N n:ℕ)
  let Y : OneCampaign p M := fun n=> inTiles (s n).T
  let E :=fun i=> bp (-q.ζ*z i)
  let R n (t : OneLeafMixture p n (M*n)) := oneLeafStrength t (w n) (m n) (q.leafOld+q.ζ) (2*q.ζ) q.e ∧
    ImageLeafMixture.elder (s n) t (P n) (fun i j=> t.pin i=(s n).pin j) ∧
    pr (w n) (fun x=> Y n x ∧ P n x∧¬inTiles t.T x)≤ E n
  obtain ⟨t,ht⟩ : ∃ t: OneRhythms p M,∀ᶠ n in l,R n (t n) := by
    refine taking ?_
    filter_upwards [hw,hx] with n hn h
    exact ImageLeafMixture.elder_trim h.strength hq.early.pos.le hn.law _
  have hz := (one_trend_sizes l hl hq.hM).2
  let Q : OneCampaign p M := fun n=> inTiles (t n).T
  have ht' (i) : R i (t i) → (∀ x, Q i x → Y i x∧P i x) ∧
      pr (w i) (fun x=>Y i x∧P i x∧¬Q i x)≤E i := fun h=>⟨fun x hx=>ImageLeafMixture.ancestral h.2.1 hx,h.2.2⟩
  obtain ⟨c,hc,hcP⟩:=hb.retained
  obtain ⟨hret,hW,hd,hZ⟩:=constant_mass_trim z hz w (hw.mono fun i h=>h.law.nz)
    Y Q P (ExpSmall.bp_n hq.early.pos) (1/2) c (by norm_num) hc
    (hx.mono fun i h=>h.weight) hcP (ht.mono (fun i h=>ht' i h))
  let d : ℕ→ℝ:=fun i=>2*E i/((1/2)*c)
  have h1 : OneDurable q l m w t := by
    refine ⟨hW,?_,(1/2)*c/2,half_pos (mul_pos (by norm_num) hc),hret⟩
    filter_upwards [ht,hx] with n hn h
    refine ⟨image_strength_slide hn.1 ?_ le_rfl (by unfold onePreparationPins; omega)
      (prodW_nonneg (fun _=>one_raw_nonneg (m n))),fun i hi x hx=>?_⟩
    · unfold leafNew
      linarith [hq.early.small,(Nat.cast_nonneg q.u : 0≤(q.u:ℝ)),(Nat.cast_nonneg q.s : 0≤(q.s:ℝ))]
    obtain ⟨j,hj,hs,_⟩:=hn.2.1 i hi
    exact (h.onTile j hj x (hs hx)).2.2
  refine ⟨t,h1,⟨hb.forecast,?_⟩,ht.mono fun i h j hj x hx=> (ht' i h).1 x ⟨j,hj,hx⟩,
    d,hd,hZ.mono (fun i h => h _)⟩
  filter_upwards [ht,hx,hb.mark] with n hn he hm
  intro i hi x hx
  obtain ⟨j,hj,hs,hc,hh⟩:=hn.2.1 i hi
  have hz : (t n).rooting x=(s n).rooting x := by
    unfold ImageLeafMixture.rooting
    rw [ImageLeafMixture.poller_eq (s:=t n) hn.1.part hi hx,ImageLeafMixture.poller_eq (s:=s n) he.strength.part hj (hs hx),
      hh]
  have hH := hm j hj x (hs hx) (hc x hx)
  unfold oneEngrave oneSeems at hH ⊢; rwa [hz]

end
end Lax793645Proofs.Simplifications
