import Lax793645Proofs.Simplifications.ExactAffinePredictions
import Lax793645Proofs.Simplifications.OneExactSupportInputs
import Lax793645Proofs.Simplifications.OneQuadraticNormalForm

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap StatusAnalysis StatusAnalysis.DualAnalysis
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
variable {p : Shape} {n N c R : ℕ}

/-- Zero disagreement under the full input law is an identity at every
input, since every point has positive mass. -/
theorem one_postulates_zero_input (o : OneOrient p n N) (g : OneAugur p N)
    (w : Pdual p n) (E : Finset (Label p.b)) (h : onePostulates o g w E 0)
    (s : Label p.b) (hs : s∉E) (l : Tag p.g) (f : Flavor p.g) (y : Knobs p.g n) :
    w (useAtom p l s f y)=g l (dialed p l f y) (oneAtomKeyValue o l s (lit f l y)) := by
  by_contra he
  have hy : 0<spins p n y := by
    rw [spins]
    exact Finset.prod_pos (fun _ _=>by change 0<unif _; rw [unif_apply]; positivity)
  exact hy.not_ge ((weight_le_pr (spins_law p n).nz he).trans (h s hs l f))

/-- Exact common input identities give bounded quadratic predictors for
a whole population. No fit, majority vote, or approximation error is
used in constructing the polynomials. -/
theorem one_exact_quadratic_population (m : Mixer p n) (P : OneUnit p n N→Prop)
    (u : OneUnit p n N→Bool→Profile p n) (α : Bool→F)
    (E : OneUnit p n N→Bool→Finset (Label p.b))
    (r : Bool→Tag p.g→ℕ)
    (A : ∀ i l,OneAtomKey (p:=p) l N→ₗ[F]Vec (Fin (r i l)))
    (φ : ∀ i l,F→Vec (Fin (r i l))→F)
    (K : ℕ) (hk : ∀ x,P x→∀ i,totalRank (u x i)≤K)
    (hP : ∃ x,P x) (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j)
    (hr : 1≤p.r) (hn : 2*p.r≤n) (hroom : 4*oneScreenRank p K<p.g*p.r)
    (hE : ∀ x,P x→∀ i,((E x i).card:ℝ)<bp ((p.b:ℝ)-2*p.j))
    (hfree : ∀ x,P x→∀ i s,s∉E x i→∀ l,
      Surjective ((A i l).comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) (x i)))))
    (H : Bool→Space (OneJointKey p N))
    (hfactor : ∀ i l a b,oneJointCell (H i) a=oneJointCell (H i) b→
      A i l (oneStarKey l a)=A i l (oneStarKey l b))
    (hjoint : ∀ x,P x→∀ i s,
      Injective ((oneMixedRow (oneFreeColumns p n s) (x i)).comp (H i).subtype))
    (he : ∀ x,P x→∀ i s,s∉E x i→∀ l f y,
      oneYoke m x i (u x i) (α i) (useAtom p l s f y)=
        φ i l (dialed p l f y) (A i l (oneAtomKeyValue (x i) l s (lit f l y)))) :
    ∃ g : Bool→OneAugur p N,
      (∀ i,OneLinearAugur (g i) (2*oneScreenRank p K)) ∧
      (∀ x,P x → oneClaimed x g m (u x) α (fun _=>∅) 0) ∧
      (∀ x,P x→∀ i,(bitSupport (testerCoefficients (u x i) (α i))).card*p.r≤
        2*oneScreenRank p K) ∧
      ∃ Q : ∀ i l,Vec (Fin (r i l))→F,
        (∀ i l,Q i l∈Stocks (Fin (r i l)) 2) ∧
        (∀ i l q c,φ i l q c=Q i l c) ∧
        ∀ i l q x,g i l q x=Q i l (A i l x) := by
  classical
  choose Q γ hQ hφ hval x0 hx0 hslice using fun i=>one_common_quadratic_exact (r i) (A i)
    (φ i) P (fun x=>x i) (fun x=>oneYoke m x i (u x i) (α i)) (fun x=>E x i)
    hP hr hn (fun x hx=>hE x hx i) (fun x hx s hs=>hfree x hx i s hs)
    (fun x hx s hs=>he x hx i s hs)
  obtain ⟨g,hg',hc,hs,hzero,hv'⟩:=one_quadratic_population_of_forms m P u α r A K hk hg h3 hj hr hn hroom
    H hfactor hjoint Q γ hQ hval (fun i=>⟨x0 i,hx0 i,hslice i⟩)
  refine ⟨g,hg',hc,hs,Q,hQ,?_,hv'⟩
  intro i l q c
  simpa only [hzero i l,zero_mul,add_zero] using hφ i l q c

/-- The complete passage from exact status predictions to bounded common
quadratic predictors for the actual construction. The prepared rank
condition is imposed on the population before any pair filter. -/
theorem one_support_quadratic_population {d : OneUnit p n N→Rates}
    (Y : OneSilhouette p N c) (hY : OneFullLinearSilhouette Y R)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2)
    (m : Mixer p n) (K : ℕ) (hg : Odd p.g) (h3 : 3≤p.g) (hj : 1≤p.j)
    (hr : 1≤p.r) (hn : 2*p.r≤n) (hroom : 4*oneScreenRank p K<p.g*p.r) :
    ∃ H : Space (OneJointKey p N),dim H≤p.g*R ∧
      ∀ P : OneUnit p n N→Prop,(∃ x,P x)→
      (∀ x,P x→OnePaletteGood H x)→
      ∀ v : ∀ x,Charts p n (d x),∀ w : ∀ x i,Cell (d x i),∀ α : Bool→F,
      (∀ x,P x→∀ i,totalRank (v x i (w x i))≤K)→
      ∀ E : OneUnit p n N→Bool→Finset (Label p.b),
      (∀ x,P x→∀ i,((E x i).card:ℝ)<bp ((p.b:ℝ)-2*p.j))→
      ∀ f : Bool→Pulsar p c,
      (∀ x,P x→∀ i,ExactStatusPrediction (oneWisp p Y) (oneWake p Y m x (v x))
        i (E x i) (yokeSet (w x i) (α i)) (f i))→
      ∃ g : Bool→OneAugur p N,
        (∀ i,OneLinearAugur (g i) (2*oneScreenRank p K)) ∧
        (∀ x,P x → oneClaimed x g m (fun i=>v x i (w x i)) α (fun _=>∅) 0) ∧
        (∀ x,P x→∀ i,(bitSupport (testerCoefficients (v x i (w x i)) (α i))).card*p.r≤
          2*oneScreenRank p K) ∧
        (∀ i,g i=oneFromPulse Y (f i)) ∧
        ∀ i l q q' k,g i l q k=g i l q' k := by
  classical
  obtain ⟨r,hrank,A,hA,ι,hι,he,H,hH,B,hB,hfactor⟩:=one_full_palette_coordinates Y hY
  refine ⟨H,hH,?_⟩
  intro P hP hgood v w α hk E hE f hf
  let φ (i : Bool) (l : Tag p.g) (q : F) (z : Vec (Fin (r l))):=f i l q (ι l q z)
  have hfree (x : OneUnit p n N) (hx : P x) (i : Bool) (s : Label p.b) (l : Tag p.g) :
      Surjective ((A l).comp ((oneStarKey l).comp (oneFreeKey (oneFreeColumns p n s) (x i)))) :=
    one_palette_free_surjective H l (A l) (B l) (hB l) (hfactor l)
      (oneFreeColumns p n s) (x i) (hgood x hx i s)
  have hfac (i : Bool) (l : Tag p.g) (a b : OneJointKey p N)
      (h : oneJointCell H a=oneJointCell H b) : A l (oneStarKey l a)=A l (oneStarKey l b) := by
    rw [hfactor l a,hfactor l b,h]
  have hid (x : OneUnit p n N) (hx : P x) (i : Bool) (s : Label p.b)
      (hs : s∉E x i) (l : Tag p.g) (fl : Flavor p.g) (z : Knobs p.g n) :
      oneYoke m x i (v x i (w x i)) (α i) (useAtom p l s fl z)=
        φ i l (dialed p l fl z) (A l (oneAtomKeyValue (x i) l s (lit fl l z))) := by
    have hh:=one_exact_yoke_inputs Y hY hN hsmall i x m (v x) (E x i) (w x i) (α i)
      (f i) (hf x hx i) s hs l fl z
    unfold oneFromPulse at hh
    rw [he] at hh
    exact hh
  obtain ⟨g,hg',hclaim,hsupp,Q,hQ,hφ,hvalue⟩:=one_exact_quadratic_population m P
    (fun x i=>v x i (w x i)) α E (fun _=>r) (fun _=>A) φ K hk hP hg h3 hj hr hn hroom
    hE (fun x hx i s _ l=>hfree x hx i s l) (fun _=>H) hfac
    (fun x hx=>hgood x hx) hid
  refine ⟨g,hg',hclaim,hsupp,?_,?_⟩
  · intro i
    funext l q k
    rw [hvalue]
    unfold oneFromPulse
    rw [he]
    exact (hφ i l q (A l k)).symm
  · intro i l q q' k
    rw [hvalue,hvalue]

end
end Lax793645Proofs.Simplifications
