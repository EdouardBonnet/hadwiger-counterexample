import Lax793645Proofs.Simplifications.OneLinearPreparation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Filter PreparationParameters PredictionClass Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev OneBranch := Option (PredictionClass × Party × F × Bool)

instance oneBranchFinite : Finite OneBranch := by
  let : Fintype PredictionClass := ⟨{dusk,dawn false,dawn true,twinned,noon},by
    intro c; cases c with | dawn i=>cases i <;> simp | _=>simp⟩
  infer_instance

def preparationQuota (k : ℕ) : ℝ := 1 / ((k:ℝ)+1)

theorem quota_pos (k : ℕ) : 0 < preparationQuota k := by unfold preparationQuota; positivity

private theorem quota_anti : Antitone preparationQuota := by
  intro k j hj
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)

private theorem quota_below {a : ℝ} (ha : 0<a) : ∃ k,preparationQuota k≤a := by
  obtain ⟨k,hk⟩:=exists_nat_gt (1/a)
  refine ⟨k,(div_le_iff₀ (by positivity : 0<(k:ℝ)+1)).mpr ?_⟩
  have := (div_lt_iff₀ ha).mp hk
  nlinarith only [this,ha]

variable {p : Shape} {n N M : ℕ} {q : PreparationParameters}

/-- Finite output of preparation at a single size. The rare case gives a
lower bound on positive conditional compatibility probabilities. -/
def OneBranchAt (q : PreparationParameters) (m : Mixer p n) (w : Wgt (OneUnit p n N))
    (s : OneLeafMixture p n N) (a : ℝ) : OneBranch → Prop
  | none => ¬oneBoundedLinearPredicts q m s w 0 ∧ 0.99<pr (pairW (s.sap w) (s.sap w)) (oneSecureAt s)
  | some (c,α,r,rare) => c.lit α ∧ ∃ i : OneSage p n N,
      OneAlgebraicRows i.g (exactPredictorRows p q) ∧ oneFiniteClass i.g α=c ∧
      s.within (fun x=>oneSeems q m s x i.g (i.m x) (i.L x) α 0 ∧
        glint p (i.m x)=r ∧ (c=dusk → oneExactInk m i.m x)) ∧
      let phases := oneMatchUp (fun x=>oneMarkedDelta x (i.m x)) α r c
      let law := pairW (s.sap w) (s.sap w)
      if rare then oneCompatibilityFloor s w phases a ∧ a/((2*N:ℕ):ℝ)^4≤pr law phases ∧
          pr law (fun x=>phases x ∧ ¬oneSecureAt s x)≤0.001*pr law phases
      else a≤pr law (fun x=>phases x ∧ oneSecureAt s x)

def OnePreparedAt (q : PreparationParameters) (m : Mixer p n)
    (w : Wgt (OneUnit p n N)) (k : ℕ) : Prop :=
  ∃ s : OneLeafMixture p n N,preparationQuota k≤s.amount w ∧
    (oneLeafStrength s w m q.leafNew (2*q.ζ) (onePreparationPins q) ∧ s.within (oneFrameSide m)) ∧
    ∃ tag,OneBranchAt q m w s (preparationQuota k) tag

theorem one_prepared_mono (q : PreparationParameters) (m : Mixer p n)
    (w : Wgt (OneUnit p n N)) : Monotone (OnePreparedAt q m w) := by
  rintro k j hkj ⟨s,hm,hshape,tag,H⟩
  have h:=quota_anti hkj
  refine ⟨s,h.trans hm,hshape,tag,?_⟩
  rcases tag with _|⟨c,α,r,rare⟩
  · exact H
  obtain ⟨hl,i,hg,hc,he,hb⟩:=H
  refine ⟨hl,i,hg,hc,he,?_⟩
  cases rare
  · exact h.trans hb
  exact ⟨one_floor_mono h hb.1,(div_le_div_of_nonneg_right h (by positivity)).trans hb.2.1,hb.2.2⟩

variable {m : cycleM p} {w : OneTale p M} {l : Filter ℕ}

theorem one_quiet_certificate {s : OneRhythms p M} (hd : OneDurable q l m w s)
    (h : ∀ᶠ n in l,OneBranchAt q (m n) (w n) (s n) 0 none) :
    ∃ k,∀ᶠ n in l,OnePreparedAt q (m n) (w n) k := by
  obtain ⟨a,ha,hm⟩:=hd.retained
  obtain ⟨k,hk⟩:=quota_below ha
  exact ⟨k,by filter_upwards [hm,hd.shape,h] with n hn hs h; exact ⟨s n,hk.trans hn,hs,none,h⟩⟩

theorem one_predicted_certificate {b : OneSketch p M} (hzero : ∀ n,b.ε n=0)
    (hr : oneLinearLedger q b l) (h : oneFinished q l m w b) :
    ∃ k,∀ᶠ n in l,OnePreparedAt q (m n) (w n) k := by
  obtain ⟨s,hd,bright,out⟩:=h
  obtain ⟨a,ha,hm⟩:=hd.retained
  let i (n : ℕ) : OneSage p n (M*n) :=
    ⟨fun j=>b.g j n,b.m n,b.L n⟩
  have he : ∀ᶠ n in l,(s n).within (fun x=>oneSeems q (m n) (s n) x (i n).g
      ((i n).m x) ((i n).L x) b.α 0 ∧ glint p ((i n).m x)=b.r ∧
      (b.c=dusk → oneExactInk (m n) (i n).m x)) := by
    filter_upwards [bright.engraved] with n h
    intro leaf hl x hx
    simpa only [oneEngrave,hzero,i] using h leaf hl x hx
  rcases out with ⟨e,hpos,hout⟩|⟨e,hpos,hout⟩
  · obtain ⟨k,hk⟩:=quota_below (lt_min ha hpos)
    refine ⟨k,?_⟩
    filter_upwards [hm,hd.shape,hr,he,hout] with n hmass hs hl he hout
    refine ⟨s n,(hk.trans (min_le_left ..)).trans hmass,hs,some (b.c,b.α,b.r,false),
      bright.forecasts.light,i n,hl.1,hl.2,he,(hk.trans (min_le_right ..)).trans hout⟩
  obtain ⟨k,hk⟩:=quota_below (lt_min ha hpos)
  refine ⟨k,?_⟩
  filter_upwards [hm,hd.shape,hr,he,hout] with n hmass hs hl he hout
  refine ⟨s n,(hk.trans (min_le_left ..)).trans hmass,hs,some (b.c,b.α,b.r,true),
    bright.forecasts.light,i n,hl.1,hl.2,he,one_floor_mono (hk.trans (min_le_right ..)) hout.1,?_,hout.2.2⟩
  exact (div_le_div_of_nonneg_right (hk.trans (min_le_right ..)) (by positivity)).trans hout.2.1

/-- The two zero parities can go directly from ordinary trimmed leaves
to the final certificate when compatibility has a conditional mass floor
and the unsafe share is small. No geometric cover occurs in this lemma. -/
theorem one_direct_zero_certificate {s : OneRhythms p M} {b : OneSketch p M}
    (hl : l≤atTop) (hp : OnePlanted q p M) (hw : ∀ᶠ n in l,OneNascent q (m n) (w n))
    (hd : OneDurable q l m w s) (hb : OneBright q l m s b) (hr : oneLinearLedger q b l)
    (he : ∀ n,b.ε n=0) (hc : b.c=twinned ∨ ∃ i,b.c=dawn i ∧ b.α i=1)
    {γ : ℝ} (hγ : 0<γ) (hgood : ∀ᶠ n in l,
      oneCompatibilityFloor (s n) (w n) (oneMatchProg b n) γ ∧
      oneGleam s w b n≤0.001*oneGlow s w b n) :
    ∃ k,∀ᶠ n in l,OnePreparedAt q (m n) (w n) k := by
  let a : ℝ := 1/(4*(2*(p.g:ℝ)+1))
  have ha : 0<a := by unfold a; positivity
  apply one_predicted_certificate he hr
  refine ⟨s,hd,hb,Or.inr ⟨min γ a,lt_min hγ ha,?_⟩⟩
  filter_upwards [hgood,hd.mass.positive,hw,(one_trend_sizes l hl hp.hM).1.eventually
    (eventually_ge_atTop 1)] with n hg hm hw hN
  have law := ImageLeafMixture.sap_law hm hw.law
  exact ⟨one_floor_mono (min_le_left ..) hg.1,
    (div_le_div_of_nonneg_right (min_le_right ..) (by positivity)).trans
      (one_zero_parity_quartic_mass hp.hG hN b.c b.α b.r _ _ law hc),hg.2⟩

end
end Lax793645Proofs.Simplifications
