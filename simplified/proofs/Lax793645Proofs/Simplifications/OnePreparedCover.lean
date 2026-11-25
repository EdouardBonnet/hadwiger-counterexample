/- Cover refinement with closed one-frame pins. The finite mass
bookkeeping follows the vendored Apache-2.0 PreparedPopulationTrimming. -/
import Lax793645Proofs.Simplifications.OnePreparedTrimming

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M}
  {P : OneCampaign p M}

theorem one_plan_inc_eff {p : Shape} {n : ℕ}
    {a b : ImagePlan (Comp p.g) (OneColumn p n)} (h : a≤b) (i : Bool) :
    oneEffectivePins (oneEndpointPrimalPins a) i≤
      oneEffectivePins (oneEndpointPrimalPins b) i := by
  intro z hz
  obtain ⟨hx,he⟩:=(one_effective_mem _ _ _).mp hz
  refine (one_effective_mem _ _ _).mpr ⟨hx,fun e=>?_⟩
  exact quadratic_squares_mono (Submodule.map_mono (Submodule.map_mono (h e))) (he e)

/-- Tiny cover exists after preparing retained mass, seen on
its support. Requires each old tile contain only original support. -/
def oneNebulous (q : PreparationParameters) (l : Filter ℕ) (s : OneRhythms p M) (w : OneTale p M) (P : OneCampaign p M)
    (b : OneSketch p M) :=
   ∀ᶠ n in l,∃ T : Cov p (2*(M*n)),cdim p T≤(onePreparationCover q)∧
     ∀ x,onePotion s w P n x≠0 → covered p T (oneMarkedDelta x (b.m n x))

theorem one_hide_on (h : oneNebulous q l s w P b) (hb : OneCitable q l p M m w s b P)
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n)) :
    ∀ᶠ n in l,∃ T : Cov p (2*(M*n)),cdim p T≤(onePreparationCover q)∧∀ i ∈ (s n).T,
       ∀ x∈i,P n x→covered p T (oneMarkedDelta x (b.m n x)) := by
  classical
  filter_upwards [hb.mass.positive,hx,h] with n hn h ht
  obtain ⟨T,hT,hc⟩:=ht
  refine ⟨T,hT,fun i hi x hx hp=> hc _ ?_⟩
  have hh := (h.onTile i hi x hx).1
  unfold onePotion
  have hm : 0< (s n).amount (w n) := lt_of_lt_of_le (by norm_num) h.weight
  have hv : (s n).sap (w n) x≠0 := by
    unfold ImageLeafMixture.sap allW
    rw [onW_val,ind_one (show inTiles (s n).T x from ⟨i,hi,hx⟩),mul_one]
    exact div_ne_zero hh hm.ne'
  rw [onW_val,ind_one hp,mul_one]; exact div_ne_zero hv hn.ne'

def oneCodedPopulation (q : PreparationParameters) (l : Filter ℕ) (s : OneRhythms p M)
    (P : OneCampaign p M) (b : OneSketch p M) :=
  ∀ᶠ n in l,∃ code : OneCompatibilityCode q p n (M*n),∀ x y,
    inTiles (s n).T x ∧ P n x → inTiles (s n).T y ∧ P n y →
    (code.read (x,y) ↔ oneMatchProg b n (x,y))

def oneSpannedPopulation (q : PreparationParameters) (l : Filter ℕ) (s : OneRhythms p M)
    (P : OneCampaign p M) (b : OneSketch p M) :=
  ∀ᶠ n in l,∃ V : Space (Ambient p (2*(M*n))),dim V≤(2*(M*n))*onePreparationCover q ∧
    ∀ x,inTiles (s n).T x ∧ P n x → oneMarkedDelta x (b.m n x)∈V

theorem one_spanned_of_cover (hc : oneNebulous q l s w P b)
    (hb : OneCitable q l p M m w s b P) (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n)) :
    oneSpannedPopulation q l s P b := by
  filter_upwards [one_hide_on hc hb hx] with n hn
  obtain ⟨T,hT,hh⟩:=hn
  exact ⟨coverX p T,(cover_dim p T).trans (Nat.mul_le_mul_left _ hT),
    fun x ⟨⟨i,hi,hx⟩,hP⟩=>hh i hi x hx hP⟩

theorem one_coded_of_span (h : oneSpannedPopulation q l s P b) :
    oneCodedPopulation q l s P b := by
  filter_upwards [h] with n hn
  obtain ⟨V,hV,hx⟩:=hn
  obtain ⟨code,hr⟩:=one_offset_span_code V _ hV b.c b.α b.r (fun x=>oneMarkedDelta x (b.m n x))
  exact ⟨code,fun x y ha hb=>hr x y (hx x ha) (hx y hb)⟩

set_option maxHeartbeats 1800000 in
theorem one_refine_compatibility (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P)
    (hc : oneCodedPopulation q l s P b) :
    ∃ t : OneRhythms p M, OneDurable q l m w t ∧
      OneBright q l m t b ∧
      (∀ᶠ n in l,oneCodedLeaves q (t n) (oneMatchProg b n)) ∧
      ∃ d,ExpSmall l (fun n=> ((2*(M*n):ℕ):ℝ)) d ∧
        ∀ᶠ n in l,oneCharm s w P b n-d n ≤ oneGlow t w b n := by
  classical
  let N (n:ℕ) := M*n; let z (n:ℕ):ℝ:=(2*N n:ℕ)
  let Y : OneCampaign p M := fun n=> inTiles (s n).T
  let E := fun i => bp (-(z i)) + bp (-q.ζ*z i)
  let R n (t : OneLeafMixture p n (M*n)) := oneLeafStrength t (w n) (m n)
    (q.leafOld+q.u+q.s+1) q.ζ (onePreparationPins q) ∧ pr (w n) (fun x=> Y n x ∧ P n x∧¬inTiles t.T x)≤ E n ∧
    ∃ code : OneCompatibilityCode q p n (M*n),
      (∀ x y,Y n x ∧ P n x → Y n y ∧ P n y → (code.read (x,y) ↔ oneMatchProg b n (x,y))) ∧
      ImageLeafMixture.elder (s n) t (P n) (fun i j=>((s n).pin j).sp≤(t.pin i).sp ∧
        ∀ x∈i,∀ y∈i,code.label x=code.label y)
  obtain ⟨t,ht⟩ : ∃ t: OneRhythms p M,∀ᶠ n in l,R n (t n) := by
    refine taking ?_
    filter_upwards [hw,hx,hc,hq.wrap.filter_mono hl,
      ((one_trend_sizes l hl hq.hM).1.eventually (eventually_gt_atTop 0)),hb.mark]
      with n hn h ht hZ hN hh
    obtain ⟨code,hL⟩:=ht
    have he := hq.early
    have hcount : num (Fin code.count)≤bp (((q.u:ℝ)-1)*(2*(M*n))) := by
      simp only [num,Fintype.card_fin]
      exact code.fits.trans (bp_le (by
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using hZ.2.2.1))
    obtain ⟨t,h1,h2,h3⟩ := one_refine_leaf_labels h.strength he.pos hn.law (P n) code.label
      he.small (by omega) (hZ.2.2.2.1 _) he.bigS (by simpa only [Nat.cast_mul] using hcount)
    exact ⟨t,h1,by simpa only [Y,E,z,N,Nat.cast_mul,Nat.cast_ofNat] using h3,code,hL,h2⟩
  have hz : Tendsto z l atTop := (one_trend_sizes l hl hq.hM).2
  let Q : OneCampaign p M := fun n=> inTiles (t n).T
  have ht' (i) : R i (t i) → (∀ x, Q i x → Y i x∧P i x) ∧
      pr (w i) (fun x=>Y i x∧P i x∧¬Q i x)≤E i := by
    rintro ⟨h,h',code,hi,hg⟩; exact ⟨fun x hx=> ImageLeafMixture.ancestral hg hx,h'⟩
  have hE : ExpSmall l z E := by
    unfold E
    convert ((ExpSmall.bp_n zero_lt_one).add hz (ExpSmall.bp_n hq.early.pos)) using 1
    simp
  obtain ⟨c,hc,hcP⟩:=hb.retained
  obtain ⟨hret,hW,hd,hZ⟩:=constant_mass_trim z hz w (hw.mono fun i h=>h.law.nz)
    Y Q P hE (1/2) c (by norm_num) hc
    (hx.mono fun i h=>h.weight) hcP (ht.mono (fun i h=>ht' i h))
  let d : ℕ→ℝ:=fun i=>2*E i/((1/2)*c)
  have h1 : OneDurable q l m w t := by
    refine ⟨hW,?_,(1/2)*c/2,half_pos (mul_pos (by norm_num) hc),hret⟩
    filter_upwards [ht,hx] with n hn h
    obtain ⟨hi,_,code,hC,hL⟩:=hn
    refine ⟨image_strength_slide hi ?_ ?_ le_rfl
      (prodW_nonneg (fun _=>one_raw_nonneg (m n))),fun i hi x hx=>?_⟩
    · unfold leafNew; linarith
    · linarith only [hq.early.pos]
    obtain ⟨j,hj,hs,_⟩:=hL i hi
    exact (h.onTile j hj x (hs hx)).2.2
  have he (i : ℕ) (h : OneEntered q (m i) (w i) (s i)) (j) (hj:j∈(s i).T)
      (x) (hx:x∈j) : (s i).rooting x=((s i).pin j).sp :=
    congrArg ImagePin.sp (ImageLeafMixture.poller_eq (s:=s i) h.strength.part hj hx)
  refine ⟨t,h1,⟨hb.forecast,?_⟩,?_,d,hd,hZ.mono (fun i h=>h _)⟩
  · filter_upwards [ht,hx,hb.mark] with n hn he' hm
    intro i hi x hx
    obtain ⟨hT,_,code,_,hL⟩:=hn
    obtain ⟨j,hj,hs,hc,hV⟩:=hL i hi
    have hz : (s n).rooting x≤(t n).rooting x := by
      rw [he n he' j hj x (hs hx),ImageLeafMixture.rooting,ImageLeafMixture.poller_eq (s:=t n) hT.part hi hx]
      exact hV.1
    obtain ⟨⟨hE,hA⟩,he,hy⟩:=hm j hj x (hs hx) (hc x hx)
    exact ⟨⟨fun i=>⟨(hE i).1,one_plan_inc_eff hz _ ((hE i).2)⟩,hA⟩,he,hy⟩
  · filter_upwards [ht] with n hn
    obtain ⟨_,_,code,hC,hL⟩:=hn
    refine ⟨code,fun i hi=>?_,fun x y hx hy=>hC x y
      (ImageLeafMixture.ancestral hL hx) (ImageLeafMixture.ancestral hL hy)⟩
    obtain ⟨_,_,_,_,_,hc⟩:=hL i hi
    exact hc

end
end Lax793645Proofs.Simplifications
