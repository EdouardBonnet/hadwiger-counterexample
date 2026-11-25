/- Phase-to-compatibility assembly for the one-frame construction.
The finite conditioning proof follows the vendored Apache-2.0
PhasePreparedOutcomes, using the new phase and rank bounds. -/
import Lax793645Proofs.Simplifications.OnePreparedOutcomes
import Lax793645Proofs.Simplifications.OnePreparedCover
import Lax793645Proofs.Simplifications.OnePreparedPhase
import Lax793645Proofs.Simplifications.OneTinyCompatibility
import Lax793645Proofs.Simplifications.OneMarkedOffsetMass

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M} {b : OneSketch p M}
  {P : OneCampaign p M}

def oneFinished (q : PreparationParameters) (l : Filter ℕ) (m : cycleM p)
    (w : OneTale p M) (b : OneSketch p M):=
  ∃ t : OneRhythms p M,OneDurable q l m w t ∧ OneBright q l m t b ∧
    (oneGlowOutcome l w t b ∨ oneGlimmer q l w t b)

theorem one_by_torch (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P)
    (hc : ∀ᶠ n in l,0.05 ≤ oneCharm s w P b n) :
    oneFinished q l m w b := by
  obtain ⟨t,hT,h1,h2,e,he,hF⟩:= one_drop_harvest hl hq hw hx hb
  refine ⟨t,hT,h1,Or.inl (hT.kindles hl hq hw ?_)⟩
  filter_upwards [hF,hc,(he.lim (one_trend_sizes l hl hq.hM).2).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ) < 0.01))]
    with n hn ht hv
  linarith only [hn,ht,hv]


theorem one_by_glitter (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P) (hn : oneCodedPopulation q l s P b)
    {δ : ℝ} (hδ : 0<δ)
    (hc : ∀ᶠ n in l, δ/((2*(M*n):ℕ):ℝ)^4 ≤ oneCharm s w P b n) :
    oneFinished q l m w b := by
  obtain ⟨t,hT,h1,h2,e,he,hF⟩:= one_refine_compatibility hl hq hw hx hb hn
  let z (n:ℕ):=((2*(M*n):ℕ):ℝ)
  have hz := (one_trend_sizes l hl hq.hM).2
  have hi : ∀ᶠ n in l,e n * (z n)^4 <δ/2 :=
    ((he.poly hz 4).lim hz).eventually (gt_mem_nhds (half_pos hδ))
  refine ⟨t,hT,h1,Or.inr (hT.coded_rare_pairs hl hq hw h2 (half_pos hδ) ?_)⟩
  filter_upwards [hF,hc,hz.eventually (eventually_gt_atTop 0),hi] with n hn ht hv h'
  have hz : 0< z n := hv
  have he := (lt_div_iff₀ (show 0 < (z n)^4 from by positivity)).mpr h'
  change (δ/2)/(z n)^4 ≤ _
  change δ/(z n)^4 ≤ _ at ht
  rw [show (δ/2)/(z n)^4= (δ/(z n)^4)/2 from by ring] at he ⊢
  linarith only [hn,ht,he]


set_option maxHeartbeats 1000000 in
theorem one_out_by_mix (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P)
    (hm : ∀ᶠ n in l, oneTonalMix (fun x=>oneMarkedDelta x (b.m n x)) (onePotion s w P n)) :
    oneFinished q l m w b := by
  classical
  refine one_by_torch hl hq hw hx hb ?_
  filter_upwards [hm,hb.on_law hl hq hw hx] with n hn ht
  obtain ⟨v,hv⟩:= meet b.c b.α b.r
  apply (one_mix_pattern p _ _ ht hn v).le.trans
  refine pr_mono (pairW_law ht ht).nz (fun x h=>?_); unfold oneMatchProg oneMatchUp; rw [h]; exact hv


/-- Distinct active predictions put no restriction on the phase. -/
theorem one_unrestricted_class (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P) (he : b.c=noon) :
    oneFinished q l m w b := by
  refine one_by_torch hl hq hw hx hb ?_
  filter_upwards [hb.on_law hl hq hw hx] with n hn
  unfold oneCharm oneMatchProg oneMatchUp
  rw [he]
  simp [compatible, (pairW_law hn hn).total]
  norm_num

/-- Both zero reciprocal parities have a direct ambient rank bound.
Finite labels give the conditional probability floor for these rare pairs. -/
theorem one_zero_parity_outcome (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P) (hc : oneCodedPopulation q l s P b)
    (hclass : b.c=twinned ∨ ∃ i,b.c=dawn i ∧ b.α i=1) :
    oneFinished q l m w b := by
  let v := onePotion s w P
  refine one_by_glitter hl hq hw hx hb hc (δ:=1/(4*(2*(p.g:ℝ)+1))) (by positivity) ?_
  filter_upwards [hb.on_law hl hq hw hx,(one_trend_sizes l hl hq.hM).1.eventually
    (eventually_ge_atTop 1)] with n hn hN
  exact one_zero_parity_quartic_mass hq.hG hN b.c b.α b.r _ (v n) hn hclass

/-- Both inactive predictions and target bit zero need only matrix rank
and the finite labels of the offset span. -/
theorem one_four_zero_outcome (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P) (hs : oneSpannedPopulation q l s P b)
    (he : b.c=dusk) (hz : b.r=0) : oneFinished q l m w b := by
  let d : ℝ:=onePreparationCover q
  let δ : ℝ:=1/(4*(d+1)^4)
  have hd : 0≤d:=Nat.cast_nonneg _
  refine one_by_glitter hl hq hw hx hb (one_coded_of_span hs) (δ:=δ) (by dsimp [δ]; positivity) ?_
  filter_upwards [hx,hb.on_law hl hq hw hx,hb.mark,hs,
    (one_trend_sizes l hl hq.hM).1.eventually (eventually_ge_atTop 1)] with n hE hW hmark hV hN
  obtain ⟨V,hr,hV⟩:=hV
  let w':=onePotion s w P n
  have support (x) (hx : w' x≠0) : inTiles (s n).T x ∧ P n x := by
    obtain ⟨hp,ha⟩:=onW_ne hx
    exact ⟨(ImageLeafMixture.present ha).1,hp⟩
  have diag (x) (hx : w' x≠0) (i : Bool) : joinPhase p (oneListens x) (unary i)
      (oneMarkedDelta x (b.m n x))=0 := by
    obtain ⟨⟨j,hj,hxj⟩,hp⟩:=support x hx
    obtain ⟨⟨hpin,_⟩,_,hink⟩:=hmark j hj x hxj hp
    exact one_diag_dusk_endpoint (m n) (b.m n) x
      (fun i=>((one_effective_mem _ _ _).mp (hpin i).2).1) (hink he)
      (hE.onTile j hj x hxj).2.2 i
  have h:=one_four_zero_span (fun x=>oneMarkedDelta x (b.m n x)) w' hW V
    (fun x h=>hV x (support x h)) diag
  unfold oneCharm oneMatchProg oneMatchUp
  rw [he,hz]
  apply le_trans _ h
  let z : ℝ:=((2*(M*n):ℕ):ℝ)
  have h1 : 1≤z:=by dsimp only [z]; exact_mod_cast (show 1≤2*(M*n) by omega)
  have hr' : (dim V:ℝ)≤z*d:=by dsimp only [z,d]; exact_mod_cast hr
  have hden : (dim V:ℝ)+1≤(d+1)*z := by linarith only [hr',h1]
  change δ/z^4≤_
  calc δ/z^4 = 1/(4*((d+1)*z)^4) := by dsimp only [δ]; rw [div_div,mul_pow,mul_assoc]
       _ ≤ _ := by gcongr

/-- A set containing more than half the population must contain a compatible
pair from the support. The two units can coincide if their readings allow it. -/
def oneHalfCrossing (s : OneRhythms p M) (w : OneTale p M) (P : OneCampaign p M)
    (b : OneSketch p M) (n : ℕ) : Prop :=
  let μ := onePotion s w P n
  ∀ I : OneUnit p n (M*n) → Prop, 1/2 < pr μ I →
    ∃ x, I x ∧ μ x ≠ 0 ∧ ∃ y, I y ∧ μ y ≠ 0 ∧ oneMatchProg b n (x,y)

/-- An algebraic sufficient condition: offsets of a subset with no compatible
pair fit in a space of dimension at most half the ambient vector dimension. -/
def oneIncompatibleSpanBound (s : OneRhythms p M) (w : OneTale p M) (P : OneCampaign p M)
    (b : OneSketch p M) (n : ℕ) : Prop :=
  let μ := onePotion s w P n
  ∀ I : OneUnit p n (M*n) → Prop,
    (∀ x, I x → μ x ≠ 0 → ∀ y, I y → μ y ≠ 0 → ¬oneMatchProg b n (x,y)) →
      ∃ V : Space (Ambient p (2*(M*n))), dim V ≤ M*n ∧
        ∀ x, I x → μ x ≠ 0 → oneMarkedDelta x (b.m n x) ∈ V

theorem OneDosed.crossing_of_span_bound (h : OneDosed q l m w s b P) (hl : l ≤ atTop)
    (hq : OnePlanted q p M) (hw : ∀ᶠ n in l, OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l, OneEntered q (m n) (w n) (s n))
    (hne : ∀ᶠ n in l, ∀ x, P n x → oneMarkedDelta x (b.m n x) ≠ 0) :
    ∀ᶠ n in l, oneIncompatibleSpanBound s w P b n → oneHalfCrossing s w P b n := by
  have ht := (trend_sizes l hl (M:=M) hq.hM).1
  filter_upwards [h.offset_span_dispersion hl hq hw hx, hne,
    (h.citable hl hq.hM).on_law hl hq hw hx,ht.eventually (eventually_ge_atTop 4)]
    with n hd hn hμ hlarge hspan I hI
  classical
  by_contra! hbad
  obtain ⟨V,hV,hinside⟩ := hspan I hbad
  have hm := (pr_mono_support (onePotion s w P n) hμ.nz
    (fun x hw (hi : I x) => And.intro (hinside x hi hw) (hn x (onW_ne hw).1))).trans (hd V hV)
  have hhalf : bp (-(1/4:ℝ)*(M*n : ℕ)) ≤ 1/2 := by
    rw [show (1/2:ℝ) = bp (-1) by rw [bp_neg,bp_one]; norm_num]
    apply bp_le
    linarith only [show (4:ℝ) ≤ (M*n:ℕ) by exact_mod_cast hlarge]
  exact (not_lt_of_ge (hm.trans hhalf)) hI

/-- A qualitative pair-existence test suffices for the quantitative rare
branch on an affordable offset span, including the two prescribed-one cases. -/
theorem one_prescribed_one_outcome (hl : l ≤ atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l, OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l, OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P) (hs : oneSpannedPopulation q l s P b)
    (hc : (∃ i, b.c = dawn i ∧ b.α i = 0) ∨ b.c = dusk ∧ b.r = 1)
    (hcross : ∀ᶠ n in l, oneHalfCrossing s w P b n) : oneFinished q l m w b := by
  let d : ℝ := onePreparationCover q
  let δ : ℝ := 1 / (16 * (d+1)^4)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  apply one_by_glitter hl hq hw hx hb (one_coded_of_span hs) (δ:=δ) (by dsimp [δ]; positivity)
  filter_upwards [hb.on_law hl hq hw hx,hs,hcross,
    (one_trend_sizes l hl hq.hM).1.eventually (eventually_ge_atTop 1)] with n hμ ⟨V,hV,hoff⟩ hc₀ hN
  let μ := onePotion s w P n
  have hsupp x (hx : μ x ≠ 0) := (onW_ne hx)
  have h := one_prescribed_one_span_alternative (fun x => oneMarkedDelta x (b.m n x))
    μ hμ V (fun x hx => hoff x ⟨(ImageLeafMixture.present (hsupp x hx).2).1,(hsupp x hx).1⟩)
    b.c b.α b.r hc (1/2) (by norm_num)
  rcases h with h | ⟨I,hI,hnone⟩
  · let z : ℝ := ((2*(M*n) : ℕ) : ℝ)
    have h1 : 1 ≤ z := by dsimp only [z]; exact_mod_cast (show 1 ≤ 2*(M*n) by omega)
    have hr : (dim V : ℝ) ≤ z*d := by dsimp only [z,d]; exact_mod_cast hV
    have hden : (dim V : ℝ)+1 ≤ (d+1)*z := by linarith only [h1,hr]
    apply le_trans _ h
    change δ/z^4 ≤ _
    calc δ/z^4 = (1/2 : ℝ)^2 / (4*((d+1)*z)^4) := by
           dsimp only [δ]; rw [div_div,mul_pow]; field_simp; ring
         _ ≤ _ := by gcongr
  obtain ⟨x,hx,hx',y,hy,hy',hxy⟩ := hc₀ I (by norm_num at hI; exact hI)
  exact (hnone x hx hx' y hy hy' hxy).elim

set_option maxHeartbeats 1400000 in
theorem one_out_by_cover (hl : l≤atTop) (hq : OnePlanted q p M)
    (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hx : ∀ᶠ n in l,OneEntered q (m n) (w n) (s n))
    (hb : OneCitable q l p M m w s b P)
    (hm : ∀ᶠ n in l, oneTonalTiny (fun x=>oneMarkedDelta x (b.m n x)) (onePotion s w P n) q.d) :
    oneFinished q l m w b := by
  classical
  let v:= onePotion s w P
  have cover : oneNebulous q l s w P b:= hm.mono (fun i h=> by
    obtain ⟨T,h1,h2,h3⟩:= h
    exact ⟨oneSymCov T,by rw [one_sym_cov_dimension]; exact Nat.mul_le_mul_left 2 h1,h2⟩)
  have span:=one_spanned_of_cover cover hb hx
  have hc:=one_coded_of_span span
  have hv := hb.on_law hl hq hw hx
  cases he : b.c with
  | noon => exact one_unrestricted_class hl hq hw hx hb he
  | dawn i =>
    by_cases hi : b.α i=1
    · exact one_zero_parity_outcome hl hq hw hx hb hc (Or.inr ⟨i,he,hi⟩)
    let z (n : ℕ):=((2*(M*n):ℕ):ℝ); have hz := (one_trend_sizes l hl hq.hM).2
    have ht : ∀ᶠ n in l,bp (-0.24*z n)<0.1 :=
      (((bp_tendsto_zero (by norm_num)).comp hz).eventually (gt_mem_nhds (by norm_num)))
    refine one_by_torch hl hq hw hx hb ?_
    filter_upwards [hv,ht,hm] with n hn ht hk
    unfold oneCharm oneMatchProg; rw [he]
    obtain ⟨_,_,_,bias⟩:=hk
    apply le_trans (by norm_num : (0.05:ℝ)≤0.4)
    exact one_singleton_bias_mass p _ _ hn _ _ _ ((bias i _).trans (by
      simpa only [z,Nat.cast_mul,Nat.cast_ofNat] using ht.le))
  | twinned => exact one_zero_parity_outcome hl hq hw hx hb hc (Or.inl he)
  | dusk =>
    by_cases hz : b.r=0
    · exact one_four_zero_outcome hl hq hw hx hb span he hz
    obtain ⟨δ,hδ,hH⟩:= eventually_ambient_pattern_margin p.g
    refine one_by_glitter hl hq hw hx hb hc hδ ?_
    filter_upwards [hx,hv,hm,hb.mark,(one_trend_sizes l hl hq.hM).1.eventually hH]
      with n hn ht hv h hH
    apply hH.trans
    unfold oneCharm oneMatchProg oneMatchUp; rw [he]
    have hd : ∀ x,onePotion s w P n x≠0 →
        joinPhase p (oneListens x) allSide (oneMarkedDelta x (b.m n x))=0 := by
      intro x hx
      obtain ⟨hp,hx⟩:=onW_ne hx
      obtain ⟨⟨i,hi,hx⟩,_⟩:=ImageLeafMixture.present hx
      obtain ⟨⟨hE,h1⟩,h2,h3⟩:=h i hi x hx hp
      exact one_diag_dusk (m n) (b.m n) x
        (fun i=>((one_effective_mem _ _ _).mp (hE i).2).1) (h3 he)
        (hn.onTile i hi x hx).2.2
    obtain ⟨_,_,_,bias⟩:=hv
    have pattern := one_four_pattern_ambient _ _ ht hd b.r (bp_pos _).le bias
    rw [one_ambient_dimension hq.hG] at pattern
    simpa only [Nat.cast_mul,Nat.cast_ofNat,compatible] using pattern


end
end Lax793645Proofs.Simplifications
