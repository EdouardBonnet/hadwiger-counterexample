import Lax793645Proofs.Simplifications.OneExactSupportExtraction
import Lax793645Proofs.Simplifications.OneFinitePredictions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis OneAppearance Function LinearMap Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem image_point_mass_le {A B : Type} [Fintype A]
    (w : Wgt A) (hw : ∀ x,0≤w x) (f : A→B) (x : A) :
    w x≤mapW w f (f x) := by
  have hh:=pr_mono hw (p:=fun y=>y=x) (q:=fun y=>f y=f x)
    (fun y h=>congrArg f h)
  simpa only [pr_point',mapW] using hh

theorem stained_point_positive {A B : Type} [Fintype A]
    (w : Wgt A) (hw : ∀ x,0≤w x) (f : A→B) (x : A) (hx : 0<w x) :
    0<stained w f (f x) x := by
  have hmass:=hx.trans_le (image_point_mass_le w hw f x)
  rw [stained,if_pos hmass.ne',onW_val,ind_one rfl,mul_one]
  exact div_pos hx hmass

variable {p : Shape} {n N c R : ℕ}

/-- Every color reached by a key has positive reference mass. This
uses full linear cells, so it makes no assumption about empirical
closeness of the orientation's key law. -/
theorem one_full_reference_positive (Y : OneSilhouette p N c)
    (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (l : Tag p.g) (q : F) (k : OneAtomKey (p:=p) l N) :
    0<oneWisp p Y l q (Y l q k) := by
  classical
  obtain ⟨r,hr,L,hL,ι,hι,he⟩:=full_linear_coordinates (hY l)
  have hrow : bp (-(R:ℝ))/2≤bp (-(r:ℝ))/2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply bp_le
    exact neg_le_neg (by exact_mod_cast hr)
  have hcell:=one_full_cell_reference l q L hL (hN l) ((hsmall l).trans hrow) (L k)
  have hpos : 0<(unif (L k):ℝ)/2 := by
    rw [unif_apply]
    positivity
  have hν : SubLaw (oneLawOmega p N l q):=
    mapW_sub (oneAtomSplit l N).symm (unifOn_sub _)
  have hpoint:=image_point_mass_le (mapW (oneLawOmega p N l q) L)
    (mapW_sub L hν).nz (ι q) (L k)
  have heq : (ι q ∘ L)=Y l q := funext (fun k=>(he q k).symm)
  rw [mapW_nested,heq] at hpoint
  change 0<mapW (oneLawOmega p N l q) (Y l q) (Y l q k)
  rw [he q k]
  exact (hpos.trans_le hcell.1).trans_le hpoint

/-- Every actual input occurs with positive mass in its conditional
status table. There is no statistical approximation in this step. -/
theorem one_actual_status_positive {d : ℕ} (x : Appearance p)
    (Y : OneSilhouette p N c) (i : Nodes) (o : OneUnit p n N)
    (m : Mixer p n) (v : Ax p n d) (z : Knobs p.g n)
    (hq : dialed p x.l x.f z=x.q) :
    0<oneReflected x Y i o m v (oneShowTag x Y (o i) z) (oneProfile x i o m v z) := by
  have hμ:=spins_law p n
  have hz : 0<spins p n z := by
    rw [spins]
    exact Finset.prod_pos (fun _ _=>by change 0<unif _; rw [unif_apply]; positivity)
  have hmass : 0<pr (spins p n) (fun y=>dialed p x.l x.f y=x.q) := by
    have hh:=pr_mono hμ.nz (p:=fun y=>y=z) (q:=fun y=>dialed p x.l x.f y=x.q)
      (fun y hy=>hy.symm ▸ hq)
    rw [pr_point'] at hh
    exact hz.trans_le hh
  have hw : 0<x.wit n z := by
    change 0<onW (spins p n) (fun y=>dialed p x.l x.f y=x.q) z
    rw [onW_val,ind_one hq,mul_one]
    exact div_pos hz hmass
  have hW : IsLaw (x.wit n):=on_law hμ.nz hmass
  have hst:=stained_point_positive (x.wit n) hW.nz (oneShowTag x Y (o i)) z hw
  exact hst.trans_le (image_point_mass_le _ (stained_law _ hW _).nz _ z)

/-- An exact status prediction is an identity at every nominal input
and every surviving label. It does not incur a query-comparison error. -/
theorem one_exact_status_input {d : Rates} (Y : OneSilhouette p N c)
    (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Charts p n d)
    (A : Finset (Label p.b)) (a : RhymeSet (d i)) (f : Pulsar p c)
    (h : ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i A a f)
    (l : Tag p.g) (s : Label p.b) (hs : s∉A) (fl : Flavor p.g) (z : Knobs p.g n) :
    let x : Appearance p:=⟨l,s,fl,dialed p l fl z⟩
    a.soot x (oneProfile x i o m (v i) z)=
      f l (dialed p l fl z) (Y l (dialed p l fl z) (oneFace x (o i) z)) := by
  let x : Appearance p:=⟨l,s,fl,dialed p l fl z⟩
  have hx : x.apt := by
    refine ⟨scan p l fl z,?_,rfl⟩
    intro j hj
    unfold scan
    rw [if_neg hj]
  exact h x hs hx _ (one_full_reference_positive Y hY hN hsmall l _ _)
    _ (one_actual_status_positive x Y i o m (v i) z rfl)

/-- In particular, the scalar predictor of the internal bit is an exact
functional identity on every surviving query input. -/
theorem one_exact_yoke_inputs {d : Rates} (Y : OneSilhouette p N c)
    (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (i : Nodes) (o : OneUnit p n N) (m : Mixer p n) (v : Charts p n d)
    (A : Finset (Label p.b)) (w : Cell (d i)) (α : F) (f : Pulsar p c)
    (h : ExactStatusPrediction (oneWisp p Y) (oneWake p Y m o v) i A (yokeSet w α) f) :
    ∀ s,s∉A→∀ l fl z,oneYoke m o i (v i w) α (useAtom p l s fl z)=
      oneFromPulse Y f l (dialed p l fl z) (oneAtomKeyValue (o i) l s (lit fl l z)) := by
  intro s hs l fl z
  let x : Appearance p:=⟨l,s,fl,dialed p l fl z⟩
  have hh:=one_exact_status_input Y hY hN hsmall i o m v A (yokeSet w α) f h l s hs fl z
  change (yokeSet w α).soot x (oneProfile x i o m (v i) z)=_ at hh
  rw [one_lyrically i o m v w α x z] at hh
  exact hh

end
end Lax793645Proofs.Simplifications
