import Lax793645Proofs.Simplifications.OneGenericInputs
import Lax793645Proofs.Simplifications.GenericStatusSpans
import Lax793645Proofs.Simplifications.OneStatusContinuation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis Club Guild Function LinearMap Finset Matrix Submodule
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {n N r K c R : ℕ} {d e : Rates}
variable {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
variable {β δ η : ℝ}

open OneAppearance

theorem one_generic_status_input {d : Rates} (Y : OneSilhouette p N c)
    (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Charts p n d)
    (A : Finset (Label p.b)) (a : RhymeSet (d i)) (f : Pulsar p c)
    (h : GenericStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i A a f)
    (l : Tag p.g) (s : Label p.b) (hs : s∉A) (z : Knobs p.g n) :
    let x : Appearance p:=⟨l,s,Flavor.full,dialed p l Flavor.full z⟩
    a.soot x (oneProfile x i o m (v i) z)=
      f l (dialed p l Flavor.full z) (Y l (dialed p l Flavor.full z) (oneFace x (o i) z)) := by
  let x : Appearance p:=⟨l,s,Flavor.full,dialed p l Flavor.full z⟩
  have hx : x.apt := by
    refine ⟨scan p l Flavor.full z,?_,rfl⟩
    intro j hj
    unfold scan
    rw [if_neg hj]
  exact h x hs hx rfl _ (one_full_reference_positive Y hY hN hsmall l _ _)
    _ (one_actual_status_positive x Y i o m (v i) z rfl)


def OneGenericStatusContinues (Y : OneSilhouette p N r) (m : Mixer p n) (B : ℕ)
    (o : OneUnit p n N) : Prop :=
  ∀ d : Rates,∀ v : Charts p n d,
    ∀ i E,E.card≤B→∀ a f,
      GenericStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i E a f→
      ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i ∅ a f

/-- Polynomial continuation applies to every edge parity, including
relations that do not predict the internal status bit. -/
theorem one_generic_status_continuation_control (Y : OneSilhouette p N r)
    (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (m : Mixer p n) (B : ℕ) (hp : 1≤p.r) (hn : 2*p.r≤n)
    (hB : (B:ℝ)<bp ((p.b:ℝ)-2*p.j)) :
    ∃ H : Space (OneJointKey p N),dim H≤p.g*R ∧
      ∀ o : OneUnit p n N,OnePaletteGood H o→OneGenericStatusContinues Y m B o := by
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
  have hgeneric (s : Label p.b) (hs : s∉E) (l : Tag p.g) (z : Knobs p.g n) :
      w (useAtom p l s Flavor.full z)=φ l (dialed p l Flavor.full z)
        (A l (oneAtomKeyValue (o i) l s (lit Flavor.full l z))) := by
    let x : Appearance p:=⟨l,s,Flavor.full,dialed p l Flavor.full z⟩
    have hh:=one_generic_status_input Y hY hN hsmall i o m v E a f hf l s hs z
    change a.soot x (oneProfile x i o m (v i) z)=_ at hh
    rw [one_rhyme_soot] at hh
    change w (useAtom p l s Flavor.full z)+a.gamma*dialed p l Flavor.full z=
      f l (dialed p l Flavor.full z) (Y l (dialed p l Flavor.full z) (oneAtomKeyValue (o i) l s (lit Flavor.full l z))) at hh
    rw [he] at hh
    calc
      _=(w (useAtom p l s Flavor.full z)+a.gamma*dialed p l Flavor.full z)+a.gamma*dialed p l Flavor.full z := by
        rw [add_assoc,char_two,add_zero]
      _=φ l (dialed p l Flavor.full z) (A l (oneAtomKeyValue (o i) l s (lit Flavor.full l z))) :=
        congrArg (fun t=>t+a.gamma*dialed p l Flavor.full z) hh
  have hid (s : Label p.b) (hs : s∉E) (l : Tag p.g) (fl : Flavor p.g) (z : Knobs p.g n) :
      w (useAtom p l s fl z)=φ l (dialed p l fl z)
        (A l (oneAtomKeyValue (o i) l s (lit fl l z))) :=
    one_generic_identity_all (o i) (fun l q k=>φ l q (A l k)) w l s
      (hgeneric s hs l) fl z
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
