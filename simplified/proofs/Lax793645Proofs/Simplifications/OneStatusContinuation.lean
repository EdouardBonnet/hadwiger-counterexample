import Lax793645Proofs.Simplifications.ExactSupportSpanStability
import Lax793645Proofs.Simplifications.ExactAffinePredictions
import Lax793645Proofs.Simplifications.OneExactSupportInputs

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function Finset Matrix LinearMap Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {r : ℕ} {d : Rates}

open OneAppearance
variable {n N R : ℕ}

def oneRhymeFunctional (m : Mixer p n) (o : OneUnit p n N)
    (v : Charts p n d) (i : Nodes) (a : RhymeSet (d i)) : Pdual p n :=
  a.bit • oneInner o i+Tsym m (v i a.coal)+(a.bit+a.headBit) • role p n

theorem one_rhyme_soot (m : Mixer p n) (o : OneUnit p n N)
    (v : Charts p n d) (i : Nodes) (a : RhymeSet (d i))
    (x : Appearance p) (z : Knobs p.g n) :
    a.soot x (oneProfile x i o m (v i) z)=
      oneRhymeFunctional m o v i a (useAtom p x.l x.s x.f z)+a.gamma*x.q := by
  change a.bit*(oneInner o i) (useAtom p x.l x.s x.f z)+
    dotProduct a.coal (roll (v i) (Tsym m (useAtom p x.l x.s x.f z)))+
    (a.bit+a.headBit)*role p n (useAtom p x.l x.s x.f z)+a.gamma*x.q=_
  rw [dotProduct_comm,←roll_project,T_swap]
  rfl

theorem one_wit_point_positive (x : Appearance p) (z : Knobs p.g n)
    (hq : dialed p x.l x.f z=x.q) : 0<x.wit n z := by
  have hz : 0<spins p n z := by
    rw [spins]
    exact Finset.prod_pos (fun _ _=>by change 0<unif _; rw [unif_apply]; positivity)
  have hmass : 0<pr (spins p n) (fun y=>dialed p x.l x.f y=x.q) := by
    have hh:=pr_mono (spins_law p n).nz (p:=fun y=>y=z)
      (q:=fun y=>dialed p x.l x.f y=x.q) (fun y hy=>hy.symm ▸ hq)
    rw [pr_point'] at hh
    exact hz.trans_le hh
  change 0<onW (spins p n) (fun y=>dialed p x.l x.f y=x.q) z
  rw [onW_val,ind_one hq,mul_one]
  exact div_pos hz hmass

/-- Every positive reference color has positive empirical mass when
its linear coordinates are onto on the free block. -/
theorem one_reference_color_empirical (Y : OneSilhouette p N r)
    (x : Appearance p) (o : OneOrient p n N)
    (a : ℕ) (L : OneAtomKey (p:=p) x.l N→ₗ[F]Vec (Fin a))
    (ι : Vec (Fin a)→Fin r) (hY : ∀ k,Y x.l x.q k=ι (L k))
    (hfree : Surjective (onePaletteFree x o L))
    (hx : x.apt) (hp : 1≤p.r) (hn : 2*p.r≤n)
    (c : Fin r) (hc : 0<oneReference x Y c) :
    0<oneEmpirical x Y o c := by
  have hν : SubLaw (oneLawOmega p N x.l x.q):=
    mapW_sub (oneAtomSplit x.l N).symm (unifOn_sub _)
  obtain ⟨k,hk,_⟩:=exists_of_pr_pos hν.nz hc
  obtain ⟨_,_,hcells⟩:=one_palette_input_cells x o L hfree hx hp hn
  obtain ⟨z,hq,hz⟩:=hcells (L k)
  have hcolor : oneShowTag x Y o z=c := by
    change Y x.l x.q (oneFace x o z)=c
    rw [hY,one_palette_input_affine,hz,←hY,hk]
  have hm:=image_point_mass_le (x.wit n) (Appearance.witLaw hx hp hn).nz
    (oneShowTag x Y o) z
  rw [hcolor] at hm
  exact (one_wit_point_positive x z hq).trans_le hm

theorem one_status_input_converse (Y : OneSilhouette p N r)
    (m : Mixer p n) (o : OneUnit p n N) (v : Charts p n d)
    (i : Nodes) (a : RhymeSet (d i)) (f : Pulsar p r)
    (hp : 1≤p.r) (hn : 2*p.r≤n)
    (hcell : ∀ x : Appearance p,x.apt→∀ c,0<oneReference x Y c→
      0<oneEmpirical x Y (o i) c)
    (he : ∀ x : Appearance p,∀ z : Knobs p.g n,dialed p x.l x.f z=x.q→
      a.soot x (oneProfile x i o m (v i) z)=f x.l x.q (oneShowTag x Y (o i) z)) :
    ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i ∅ a f := by
  intro x _ hx c hc z hz
  have hw:=Appearance.witLaw hx hp hn
  have hm:mapW (x.wit n) (oneShowTag x Y (o i)) c≠0:=(hcell x hx c hc).ne'
  obtain ⟨y,hy,hpos⟩:=exists_of_pr_pos (stained_law (oneShowTag x Y (o i)) hw c).nz hz
  have hst : onW (x.wit n) (fun y=>oneShowTag x Y (o i) y=c) y≠0 := by
    simpa only [stained,if_pos hm] using hpos.ne'
  have hyc:=(onW_ne hst).1
  have hyq:dialed p x.l x.f y=x.q := (onW_ne (onW_ne hst).2).1
  have hid:=he x y hyq
  rw [hy,hyc] at hid
  exact hid

def OneStatusContinues (Y : OneSilhouette p N r) (m : Mixer p n) (B : ℕ)
    (o : OneUnit p n N) : Prop :=
  ∀ d : Rates,∀ v : Charts p n d,
    StatusLabelContinuation (oneWisp p Y) (oneWake p Y m o v) B

/-- Polynomial continuation applies to every edge parity, including
relations that do not predict the internal status bit. -/
theorem one_status_continuation_control (Y : OneSilhouette p N r)
    (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (m : Mixer p n) (B : ℕ) (hp : 1≤p.r) (hn : 2*p.r≤n)
    (hB : (B:ℝ)<bp ((p.b:ℝ)-2*p.j)) :
    ∃ H : Space (OneJointKey p N),dim H≤p.g*R ∧
      ∀ o : OneUnit p n N,OnePaletteGood H o→OneStatusContinues Y m B o := by
  classical
  obtain ⟨rows,hrows,A,hA,ι,hι,he,H,hH,C,hC,hfactor⟩:=one_full_palette_coordinates Y hY
  refine ⟨H,hH,?_⟩
  intro o ho d v i E hE a f hf
  let φ (l : Tag p.g) (q : F) (c : Vec (Fin (rows l))):=f l q (ι l q c)+a.gamma*q
  let w:=oneRhymeFunctional m o v i a
  have hfree (s : Label p.b) (l : Tag p.g) :
      Surjective ((A l).comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) (o i)))) :=
    one_palette_free_surjective H l (A l) (C l) (hC l) (hfactor l)
      (oneFreeColumns p n s) (o i) (ho i s)
  have hid (s : Label p.b) (hs : s∉E) (l : Tag p.g) (fl : Flavor p.g) (z : Knobs p.g n) :
      w (useAtom p l s fl z)=φ l (dialed p l fl z)
        (A l (oneAtomKeyValue (o i) l s (lit fl l z))) := by
    let x : Appearance p:=⟨l,s,fl,dialed p l fl z⟩
    have hh:=one_exact_status_input Y hY hN hsmall i o m v E a f hf l s hs fl z
    change a.soot x (oneProfile x i o m (v i) z)=_ at hh
    rw [one_rhyme_soot] at hh
    change w (useAtom p l s fl z)+a.gamma*dialed p l fl z=
      f l (dialed p l fl z) (Y l (dialed p l fl z) (oneAtomKeyValue (o i) l s (lit fl l z))) at hh
    rw [he] at hh
    calc
      _=(w (useAtom p l s fl z)+a.gamma*dialed p l fl z)+a.gamma*dialed p l fl z := by
        rw [add_assoc,char_two,add_zero]
      _=φ l (dialed p l fl z) (A l (oneAtomKeyValue (o i) l s (lit fl l z))) :=
        congrArg (fun t=>t+a.gamma*dialed p l fl z) hh
  have hsize : (E.card:ℝ)<bp ((p.b:ℝ)-2*p.j):=
    (by exact_mod_cast hE : (E.card:ℝ)≤B).trans_lt hB
  obtain ⟨Q,γ,hQ,hφ,hval,_⟩:=one_common_quadratic_exact rows A φ (fun _ : Unit=>True)
    (fun _=>o i) (fun _=>w) (fun _=>E) ⟨(),trivial⟩ hp hn
    (fun _ _=>hsize) (fun _ _ s _=>hfree s) (fun _ _=>hid)
  apply one_status_input_converse Y m o v i a f hp hn
  · intro x hx c hc
    exact one_reference_color_empirical Y x (o i) (rows x.l) (A x.l) (ι x.l x.q)
      (he x.l x.q) (hfree x.s x.l) hx hp hn c hc
  intro x z hq
  have hval':=hval () trivial x.l x.s x.f z
  rw [←hφ] at hval'
  change w (useAtom p x.l x.s x.f z)=
    f x.l (dialed p x.l x.f z) (ι x.l (dialed p x.l x.f z)
      (A x.l (oneAtomKeyValue (o i) x.l x.s (lit x.f x.l z))))+
    a.gamma*dialed p x.l x.f z at hval'
  rw [hq,←he] at hval'
  rw [one_rhyme_soot]
  change w (useAtom p x.l x.s x.f z)+a.gamma*x.q=_
  rw [hval',add_assoc,char_two,add_zero]
  rfl

end
end Lax793645Proofs.Simplifications
