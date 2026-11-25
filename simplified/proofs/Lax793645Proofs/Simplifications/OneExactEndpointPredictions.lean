import Lax793645Proofs.Simplifications.OneExactQuadraticPopulation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap StatusAnalysis StatusAnalysis.DualAnalysis
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N c R : ℕ}

/-- A single endpoint's exact status predictor already has a canonical
quadratic form. No prediction at the other endpoint is assumed. -/
theorem one_exact_endpoint_prediction (Y : OneSilhouette p N c)
    (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (m : Mixer p n) (K : ℕ) (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j)
    (hr : 1≤p.r) (hn : 2*p.r≤n) (hroom : 4*oneScreenRank p K<p.g*p.r) :
    ∃ H : Space (OneJointKey p N),dim H≤p.g*R ∧
      ∀ x : OneUnit p n N,OnePaletteGood H x→∀ d : Rates,∀ v : Charts p n d,
      ∀ i : Nodes,∀ w : Cell (d i),∀ α : F,totalRank (v i w)≤K→
      ∀ E : Finset (Label p.b),(E.card:ℝ)<bp ((p.b:ℝ)-2*p.j)→
      ∀ f : Pulsar p c,
      ExactStatusPrediction (oneWisp p Y) (oneWake p Y m x v) i E (yokeSet w α) f→
        OneLinearAugur (oneFromPulse Y f) (2*oneScreenRank p K) ∧
        (∀ l q q' k,oneFromPulse Y f l q k=oneFromPulse Y f l q' k) ∧
        onePostulates (x i) (oneFromPulse Y f) (oneYoke m x i (v i w) α) ∅ 0 := by
  classical
  obtain ⟨r,hrank,A,hA,ι,hι,he,H,hH,B,hB,hfactor⟩:=one_full_palette_coordinates Y hY
  refine ⟨H,hH,?_⟩
  intro x hgood d v i w α hk E hE f hf
  let φ (l : Tag p.g) (q : F) (z : Vec (Fin (r l))):=f l q (ι l q z)
  have hfree (s : Label p.b) (l : Tag p.g) :
      Surjective ((A l).comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) (x i)))) :=
    one_palette_free_surjective H l (A l) (B l) (hB l) (hfactor l)
      (oneFreeColumns p n s) (x i) (hgood i s)
  have hfac (l : Tag p.g) (a b : OneJointKey p N)
      (h : oneJointCell H a=oneJointCell H b) : A l (oneStarKey l a)=A l (oneStarKey l b) := by
    rw [hfactor l a,hfactor l b,h]
  have hid (s : Label p.b) (hs : s∉E) (l : Tag p.g) (fl : Flavor p.g) (z : Knobs p.g n) :
      oneYoke m x i (v i w) α (useAtom p l s fl z)=
        φ l (dialed p l fl z) (A l (oneAtomKeyValue (x i) l s (lit fl l z))) := by
    have hh:=one_exact_yoke_inputs Y hY hN hsmall i x m v E w α f hf s hs l fl z
    unfold oneFromPulse at hh
    rw [he] at hh
    exact hh
  obtain ⟨Q,γ,hQ,hφ,hval,t0,_,hslice⟩:=one_common_quadratic_exact r A φ (fun _ : Unit=>True)
    (fun _=>x i) (fun _=>oneYoke m x i (v i w) α) (fun _=>E) ⟨(),trivial⟩ hr hn
    (fun _ _=>hE) (fun _ _ s _=>hfree s) (fun _ _=>hid)
  have hval' := hval () trivial
  have hzero := (one_quadratic_endpoint_slopes H x i (v i w) α m K hk r A Q γ
    (hgood i) hfac hg h3 hj hr hn hroom hval').1
  have hform (l : Tag p.g) (q : F) (k : OneAtomKey (p:=p) l N) :
      oneFromPulse Y f l q k=Q l (A l k) := by
    unfold oneFromPulse
    rw [he]
    simpa only [hzero l,zero_mul,add_zero] using hφ l q (A l k)
  refine ⟨?_,?_,?_⟩
  · intro l
    obtain ⟨s,y,S,hs⟩:=hslice l
    have hc : HasLinearCells (fun (_ : F) c=>Q l c) (2*oneScreenRank p K) := by
      rw [hs]
      exact one_yoke_section_coordinates m x i (v i w) α K hk hg l s Flavor.full y S
    have hh:=linear_cells_precompose hc (A l)
    convert hh using 1
    funext q k
    exact hform l q k
  · intro l q q' k
    rw [hform,hform]
  · intro s _ l fl
    have hz : oneMismatch (oneFromPulse Y f) (oneYoke m x i (v i w) α) l s fl (x i)=fun _=>False := by
      funext z
      apply propext
      unfold oneMismatch
      rw [hform,hval' l s fl z,hzero l,zero_mul,add_zero]
      simp
    rw [hz,pr_false]

end
end Lax793645Proofs.Simplifications
