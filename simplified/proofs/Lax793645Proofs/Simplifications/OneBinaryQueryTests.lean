import Lax793645Proofs.Simplifications.ReducedMixers
import Lax793645Proofs.Simplifications.OneBinaryRankCalendar
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.BinaryMixingBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset Filter
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

abbrev OneCrossing (p : Shape) (l d : Tag p.g):={e : Comp p.g//inc e l ∧inc e d}
abbrev OneHarm (p : Shape) (l d : Tag p.g):=
  ReducedBits p⊕{u : Unit//Template.sharesComponent p l d}
abbrev oneAbbey (v : Template p I) : v.Chorus→Type
  | .inl i=>OneHarm p (v.t i.val.1) (v.t i.val.2)
  | .inr i=>OneCrossing p (v.t i.val.1) (v.t i.val.2)
instance (v : Template p I) (i : v.Chorus) : Fintype (oneAbbey v i):=
  i.rec (fun _=>inferInstanceAs (Fintype (OneHarm p _ _)))
    (fun _=>inferInstanceAs (Fintype (OneCrossing p _ _)))
instance (v : Template p I) (i : v.Chorus) : DecidableEq (oneAbbey v i):=Classical.typeDecidableEq _

def oneMonks (v : Template p I) (m : Mixer p n) (x : OneUnit p n N)
    (i : v.Chorus) : oneAbbey v i→Moment p n:=
  match i with
  | .inl _=>Sum.elim (fun l=>eitherM l.2 (reducedOrdered m l.1))
    (fun _=>selfM p n m.mixM+(selfM p n m.mixM)ᵀ)
  | .inr _=>fun e=>oneDuel (x true e.val) (x false e.val)

def oneChime (v : Template p I) (m : Mixer p n) (x : OneUnit p n N)
    (i : v.Chorus) (a b : Knobs p.g n) : Vec (oneAbbey v i):=
  fun j=>evmat (oneMonks v m x i j) (v.croon (v.choral.first i) a) (v.croon (v.choral.nextP i) b)
def oneChorusM (v : Template p I) (m : Mixer p n) (x : OneUnit p n N)
    (i : v.Chorus) (c : Vec (oneAbbey v i)):=∑ j,c j •oneMonks v m x i j

theorem one_chime_seq (v : Template p I) (m : Mixer p n) (x : OneUnit p n N)
    (i : v.Chorus) (c : Vec (oneAbbey v i)) (a b : Knobs p.g n) :
    dotProduct c (oneChime v m x i a b)=evmat (oneChorusM v m x i c)
      (v.croon (v.choral.first i) a) (v.croon (v.choral.nextP i) b) := by
  unfold oneChorusM dotProduct oneChime
  simp_rw [←mpair_outer,mpair_sum,mpair_smul]

def oneSameSelf (v : Template p I) (i : v.SameDuet)
    (c : Vec (oneAbbey v (.inl i))) : Vec Bool:=fun _=>
  if h : Template.sharesComponent p (v.t i.val.1) (v.t i.val.2) then c (.inr ⟨(),h⟩) else 0

theorem one_same_self_apply (v : Template p I) (i : v.SameDuet)
    (c : Vec (oneAbbey v (.inl i)))
    (j : {u : Unit//Template.sharesComponent p (v.t i.val.1) (v.t i.val.2)}) (b : Bool) :
    oneSameSelf v i c b=c (.inr j) := by
  simp only [oneSameSelf,dif_pos j.property]

theorem one_chorus_same (v : Template p I) (m : Mixer p n) (x : OneUnit p n N)
    (i : v.SameDuet) (c : Vec (oneAbbey v (.inl i))) :
    oneChorusM v m x (.inl i) c=reducedIndexedSum m (fun j=>c (.inl j))+selfSum m (oneSameSelf v i c) := by
  unfold oneChorusM
  change (∑ j : OneHarm p (v.t i.val.1) (v.t i.val.2),_)=_
  rw [Fintype.sum_sum_type]
  apply congrArg (reducedIndexedSum m (fun j=>c (.inl j))+·)
  let P:=Template.sharesComponent p (v.t i.val.1) (v.t i.val.2)
  by_cases hP : P
  · letI : Unique {u : Unit//P}:=⟨⟨⟨(),hP⟩⟩,fun _=>Subsingleton.elim _ _⟩
    change (∑ j : {u : Unit//P},_)=_
    rw [Fintype.sum_unique]
    rw [show (default : {u : Unit//P})=⟨(),hP⟩ from Subsingleton.elim _ _]
    dsimp only [P] at hP
    simp [oneMonks,selfSum,Fintype.sum_bool,oneSameSelf,hP,eitherM,smul_add]
  · letI : IsEmpty {u : Unit//P}:=⟨fun j=>hP j.property⟩
    change (∑ j : {u : Unit//P},_)=_
    dsimp only [P] at hP
    simp only [Finset.univ_eq_empty,Finset.sum_empty,selfSum,Fintype.sum_bool,
      oneSameSelf,dif_neg hP,zero_smul,zero_add]

theorem one_chorus_cross (v : Template p I) (m : Mixer p n) (x : OneUnit p n N)
    (i : v.OppDuet) (c : Vec (oneAbbey v (.inr i))) (hc : c≠0) :
    ∃ d : Vec (Comp p.g),d≠0 ∧oneChorusM v m x (.inr i) c=oneIssue d (x true) (x false) := by
  let P (e : Comp p.g):=inc e (v.t i.val.1) ∧inc e (v.t i.val.2)
  let d (e : Comp p.g):=if h:P e then c ⟨e,h⟩ else 0
  have he (e : OneCrossing p (v.t i.val.1) (v.t i.val.2)) : d e.val=c e:=dif_pos e.property
  have hd : d≠0:=fun h=>hc (funext (fun e=>by rw [←he,h]; rfl))
  refine ⟨d,hd,?_⟩
  let f (e : Comp p.g):=d e •oneDuel (x true e) (x false e)
  have hs : (∑ e : {e : Comp p.g//P e},f e.val)=∑ e : Comp p.g,f e := by
    rw [←Finset.sum_subtype (univ.filter P) (by intro e; simp) f]
    apply Finset.sum_subset (subset_univ _)
    intro e _ he
    have hn : ¬P e:=fun h=>he (mem_filter.mpr ⟨mem_univ _,h⟩)
    simp only [f,d,dif_neg hn,zero_smul]
  change (∑ e : {e : Comp p.g//P e},_)=∑ e : Comp p.g,f e
  rw [←hs]
  apply sum_congr rfl
  intro e _
  change c ⟨e.val,e.property⟩ •oneDuel (x true e.val) (x false e.val)=
    d e.val •oneDuel (x true e.val) (x false e.val)
  simp only [d,dif_pos e.property]

def oneLyrics (v : Template p I) (s : Script p I) (i : v.Chorus) : Vec (oneAbbey v i):=
  match i with
  | .inl z=>Sum.elim (fun j=>if j.2 then s z.val.1 z.val.2 (reducedSlot j.1) else s z.val.2 z.val.1 (reducedSlot j.1)) (fun _=>0)
  | .inr _=>0
def onePerforms (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : OneUnit p n N) (z : Inputs p n I):=
  listen v.choral (oneChime v m x) z=oneLyrics v s
def oneKappa (v : Template p I):=wavelength (oneAbbey v)
theorem one_kappa_pos (v : Template p I) : 0<oneKappa v:=wavelength_pos _

theorem one_choral_live (v : Template p I) (m : Mixer p n) (hm : reducedBinaryGood m)
    (x : OneUnit p n N) (hx : oneLitFire x) (hv : v.diffsel)
    (i : v.Chorus) (c : Vec (oneAbbey v i)) (hc : c≠0) :
    ∃ B,(v.f (v.choral.first i)).keeps (v.t (v.choral.first i)) B ∧
      (v.f (v.choral.nextP i)).keeps (v.t (v.choral.nextP i)) B ∧
      n≤5*blockRank B (v.s (v.choral.first i)) (v.s (v.choral.nextP i)) (oneChorusM v m x i c) := by
  cases i with
  | inl i=>
    have hh:=hv i.val.1 i.val.2 (v.choral.diff (.inl i)) i.property.1
    have hab : (fun j=>c (.inl j))≠0 ∨oneSameSelf v i c≠0 := by
      by_contra! h
      apply hc
      funext j
      cases j with
      | inl j=>exact congrFun h.1 j
      | inr j=>exact (one_same_self_apply v i c j true).symm.trans (congrFun h.2 true)
    refine ⟨Block.sharp,Flavor.keepSharp ..,Flavor.keepSharp ..,?_⟩
    rw [one_chorus_same]
    exact hm.2 _ _ hh _ _ hab
  | inr i=>
    refine ⟨Block.Z,Flavor.keepZ ..,Flavor.keepZ ..,?_⟩
    obtain ⟨d,hd,he⟩:=one_chorus_cross v m x i c hc
    rw [he]
    exact hx _ _ d hd

theorem one_resonant (v : Template p I) (m : Mixer p n) (hm : reducedBinaryGood m)
    (x : OneUnit p n N) (hx : oneLitFire x) (hv : v.diffsel)
    (w : I→Wgt (Knobs p.g n)) (hw : ∀ i,IsLaw (w i))
    (C : ℝ) (hC : 0<C) (hc : ∀ i j,w i j≤C*unif j) (s : Script p I)
    (u : I→Wgt (Knobs p.g n)) (hu : ∀ i z,|u i z|≤1) :
    |avg (prodW w) (fun z=>ind (onePerforms v s m x z)*prodW u z)-
      oneKappa v*∏ i,avg (w i) (u i)|≤C^2*bp (-(n:ℝ)/10) := by
  refine hear_band v.choral (oneChime v m x) (oneLyrics v s) w hw _
    (mul_nonneg (sq_nonneg _) (bp_pos _).le) ?_ u hu
  intro i c hc' a b ha hb
  obtain ⟨B,hB,hB',hr⟩:=one_choral_live v m hm x hx hv i c hc'
  simp_rw [vectorPhase,one_chime_seq]
  exact spark_condition _ (oneChorusM v m x i c) _ _ _ _ _ _ B hB hB' a b ha hb
    _ _ (hw _) (hw _) C hC (hc _) (hc _) hr

end
end Lax793645Proofs.Simplifications
