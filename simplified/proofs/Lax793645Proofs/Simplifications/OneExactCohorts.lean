import Lax793645Proofs.Simplifications.OnePredictionCohorts
import Lax793645Proofs.Simplifications.OneExactQuadraticPopulation
import Lax793645Proofs.Simplifications.OneCommonImageRanks

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset PreparationParameters
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N : ℕ} {q : PreparationParameters}

def exactPredictorRows (p : Shape) (q : PreparationParameters) := 2*oneScreenRank p q.e

/-- Exact common predictions have a bounded quadratic normal form.
The only deleted mass is the failure of the free-coordinate rank. -/
theorem one_algebraic_cohort (m : Mixer p n) (w : Wgt (OneUnit p n N))
    (s : OneLeafMixture p n N) (hs : OneEntered q m w s) (hw : IsLaw w)
    (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j) (hr : 1≤p.r) (hn : 2*p.r≤n)
    (hexact : 4*oneScreenRank p q.e+2*q.e*p.r<p.g*p.r)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4≤N)
    (hB : (q.B:ℝ)<bp ((p.b:ℝ)-2*p.j))
    (hsize : 64*(p.b+4)≤n) (htail : 2*bp (-(n:ℝ)/2)≤crowdSeed)
    (hside : ∀ i o,mapW (s.sap w) (fun x=>x i) o≤bp ((n:ℝ)/32)*oneRaw m N o)
    (h : ∃ g : Bool→OneAugur p N,
      (∃ R : ℕ,8*p.g*R≤n ∧ ∀ i,OneLinearAugur (g i) R) ∧
      (0.000001:ℝ)≤pr (s.sap w) (fun x=>∃ z L α,oneSeems q m s x g z L α 0)) :
    ∃ (z : OneBanners) (i : OneSage p n N),
      OneAlgebraicRows i.g (exactPredictorRows p q) ∧
      (∀ x j,totalRank (i.m x j)≤q.e) ∧
      (z.2.2=true→z.1 true=z.1 false) ∧
      crowdSeed≤pr (s.sap w) (oneTender i q m s z 0) := by
  classical
  let Inv (g : Bool→OneAugur p N):=∃ R : ℕ,8*p.g*R≤n ∧ ∀ i,OneLinearAugur (g i) R
  obtain ⟨z,i,⟨R,hR,hgR⟩,hcap,hmass⟩:=one_cohort_reserve m w s hs hw Inv h
  choose r hrA A hA φ hφ using fun j l=>independent_predictor_coordinates (hgR j l)
  choose H hH hfactor hfreeH using fun j=>one_predictor_row_space (r j) (A j) (hA j)
  let v:=s.sap w
  have hv : IsLaw v:=ImageLeafMixture.sap_law (by linarith only [hs.weight]) hw
  let Bad (j : Bool) (o : OneOrient p n N):=∃ s,
    ¬Injective ((oneMixedRow (oneFreeColumns p n s) o).comp (H j).subtype)
  let Good (x : OneUnit p n N):=∀ j,¬Bad j (x j)
  have hbad (j : Bool) : pr v (fun x=>Bad j (x j))≤bp (-(n:ℝ)/2) := by
    rw [←mapW_pr v (fun x=>x j) (Bad j)]
    have hh:=one_prepared_linear_rank m hroom hN (H j)
      (mapW v (fun x=>x j)) (hside j)
    have hdim : ∑ l,r j l≤p.g*R := by
      exact (Finset.sum_le_sum (fun l _=>hrA j l)).trans_eq (by simp [Tag])
    have hR' : 8*(p.g*R)≤n := by simpa only [Nat.mul_assoc] using hR
    have hdim' : 4*(∑ l,r j l:ℕ)≤n := by omega
    have hd : 4*((∑ l,r j l:ℕ):ℝ)≤n := by exact_mod_cast hdim'
    have hdimH : (Module.finrank F (H j):ℝ)≤(∑ l,r j l:ℕ) := by exact_mod_cast hH j
    have hn' : 64*((p.b:ℝ)+4)≤n := by exact_mod_cast hsize
    refine hh.trans ?_
    rw [show (8:ℝ)=bp 3 by norm_num [bp],←bp_add]
    exact bp_le (by linarith only [hd,hn',hdimH])
  have hgood : pr v (fun x=>¬Good x)≤crowdSeed := by
    have hh : pr v (fun x=>¬Good x)≤∑ j : Bool,pr v (fun x=>Bad j (x j)) := by
      refine (pr_mono hv.nz (fun x hx=>?_) |>.trans (pr_exists_le hv.nz _))
      simpa only [Good,not_forall,not_not] using hx
    refine (hh.trans (Finset.sum_le_sum (fun j _=>hbad j))).trans ?_
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul,Nat.cast_ofNat]
      using htail
  let P (x : OneUnit p n N):=oneTender i q m s z 0 x ∧ Good x
  have hPmass : crowdSeed≤pr v P := by
    have hh:=pr_shield hv.nz (oneTender i q m s z 0) Good
    exact (show crowdSeed≤pr v (oneTender i q m s z 0)-pr v (fun x=>¬Good x) by
      have hp:=pollen_pos
      dsimp only [crowdSeed] at *
      linarith only [hmass,hgood,hp]).trans hh
  have hP : ∃ x,P x := by
    by_contra! hh
    have hz : pr v P=0 := by simp only [pr,show P=(fun _=>False) from funext fun x=>
      propext ⟨fun h=>(hh x h).elim,False.elim⟩,ind_false,avg_zero]
    rw [hz] at hPmass
    exact (by unfold crowdSeed; linarith only [pollen_pos] : (0:ℝ)<crowdSeed).not_ge hPmass
  have hE (x : OneUnit p n N) (hx : P x) (j : Bool) :
      ((i.L x j).card:ℝ)<bp ((p.b:ℝ)-2*p.j) :=
    lt_of_le_of_lt (by exact_mod_cast (hx.1.1.1 j).1) hB
  have hfree (x : OneUnit p n N) (hx : P x) (j : Bool) (s : Label p.b)
      (_ : s∉i.L x j) (l : Tag p.g) : Surjective ((A j l).comp ((oneStarKey l).comp
        (oneFreeKey (oneFreeColumns p n s) (x j)))) := by
    apply hfreeH j (x j) s _ l
    exact not_not.mp (fun hh=>hx.2 j ⟨s,hh⟩)
  have hjoint (x : OneUnit p n N) (hx : P x) (j : Bool) (s : Label p.b) :
      Injective ((oneMixedRow (oneFreeColumns p n s) (x j)).comp (H j).subtype) :=
    not_not.mp (fun hh=>hx.2 j ⟨s,hh⟩)
  have hid (x : OneUnit p n N) (hx : P x) (j : Bool) (a : Label p.b)
      (ha : a∉i.L x j) (t : Tag p.g) (f : Flavor p.g) (y : Knobs p.g n) :
      oneYoke m x j (i.m x j) (z.1 j) (useAtom p t a f y)=
        φ j t (dialed p t f y) (A j t (oneAtomKeyValue (x j) t a (lit f t y))) := by
    rw [←hφ]
    exact one_postulates_zero_input (x j) (i.g j) _ _ (hx.1.1.2 j) a ha t f y
  obtain ⟨g',hlin,hpred,hsupport,hpoly⟩:=one_exact_quadratic_population m P i.m z.1 i.L r A φ
    q.e (fun x _ j=>hcap x j) hP hg h3 hj hr hn (by omega) hE hfree H hfactor hjoint hid
  have hconsistent : z.2.2=true→z.1 true=z.1 false := by
    intro hz
    obtain ⟨x,hx,hvx⟩:=exists_of_pr_pos hv.nz
      ((by unfold crowdSeed; linarith only [pollen_pos] : (0:ℝ)<crowdSeed).trans_le hPmass)
    obtain ⟨⟨t,ht,hxt⟩,_⟩:=ImageLeafMixture.present hvx.ne'
    have hraw:=hs.onTile t ht x hxt
    have hmem (j : Bool) : i.m x j∈Xspace p n:=
      ((one_effective_mem _ _ _).mp (hx.1.1.1 j).2).1
    have hdelta:=one_zero_delta i.m x ((hx.1.2.2).mp hz)
    apply cycle_support_consistency (i.m x true) (i.m x false) (hmem true) (hmem false)
      hg h3 (fun e=>one_common_image_tester hj (hraw.2.2 true) (hraw.2.2 false)
        (hmem true) (hmem false) hdelta e) (z.1 true) (z.1 false)
    have ha:=hsupport x hx true
    have hb:=hsupport x hx false
    have hrank:=Nat.add_le_add (hcap x true) (hcap x false)
    have hrank':=(Nat.mul_le_mul_right p.r hrank)
    have hsum : ((bitSupport (testerCoefficients (i.m x true) (z.1 true))).card+
        (bitSupport (testerCoefficients (i.m x false) (z.1 false))).card+
        totalRank (i.m x true)+totalRank (i.m x false))*p.r<p.g*p.r := by
      nlinarith only [ha,hb,hrank',hexact]
    exact (Nat.mul_lt_mul_right (by omega : 0<p.r)).mp hsum
  let i' : OneSage p n N:=⟨g',i.m,fun _ _=>∅⟩
  obtain ⟨Q,_,_,hQ⟩ := hpoly
  have hrows : OneAlgebraicRows g' (exactPredictorRows p q) :=
    ⟨hlin,fun i l q x => (hQ i l q x).trans (hQ i l 0 x).symm⟩
  refine ⟨z,i',hrows,hcap,hconsistent,hPmass.trans (pr_mono hv.nz (fun x hx=>?_))⟩
  refine ⟨⟨fun j=>⟨?_, (hx.1.1.1 j).2⟩,hpred x hx⟩,hx.1.2.1,hx.1.2.2⟩
  change (∅:Finset (Label p.b)).card≤q.B
  simp

end
end Lax793645Proofs.Simplifications
