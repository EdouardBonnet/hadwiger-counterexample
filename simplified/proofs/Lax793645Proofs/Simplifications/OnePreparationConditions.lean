import Lax793645Proofs.Simplifications.OneLeafMixtures
import Lax793645Proofs.Simplifications.OneLeafRefinement
import Lax793645Proofs.Simplifications.OnePredictionClasses
import Lax793645Proofs.Simplifications.OneCoverCompatibility
import Lax793645Proofs.Simplifications.OneInjectionCalendar
import Lax793645Proofs.Simplifications.OnePhaseCalendar
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PreparationConditions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N M : ℕ}

abbrev OneTale (p : Shape) (M : ℕ):=∀ n,Wgt (OneUnit p n (M*n))
abbrev OneRhythms (p : Shape) (M : ℕ):=∀ n,OneLeafMixture p n (M*n)
abbrev OneCampaign (p : Shape) (M : ℕ):=∀ n,OneUnit p n (M*n)→Prop
abbrev OneMarks (p : Shape) (n N : ℕ):=OneUnit p n N→Bool→Profile p n

def oneFrameSide (m : Mixer p n) (x : OneUnit p n N):=∀ i,oneFrameLaw m (x i)
def onePreparationPins (q : PreparationParameters):=q.e+q.s

/-- A symmetric cover of dimension d gives a two-sided cover of dimension 2d. -/
def onePreparationCover (q : PreparationParameters):=2*q.d

theorem one_sym_cov_dimension (S : SymCover p (2*N)) :
    cdim p (oneSymCov S)=2*oneCoverDimension S := by
  rw [cdim_sign]
  change oneCoverDimension S+oneCoverDimension S=2*oneCoverDimension S
  omega

structure OnePreparationAllows (q : PreparationParameters) : Prop where
  pos : 0<q.ζ
  small : q.ζ<1
  hL : 0≤q.L
  bigS : q.leafOld+q.u+q.ζ≤((q.ζ/6)-(q.ζ/6)/4)*q.s

structure OneNascent (q : PreparationParameters) (m : Mixer p n)
    (w : Wgt (OneUnit p n N)) : Prop where
  law : IsLaw w
  border : oneBySide w m q.L
  total : ∀ x,w x≤bp ((q.D:ℝ)*(2*N))*oneUnitRaw m N x

structure OneEntered (q : PreparationParameters) (m : Mixer p n)
    (w : Wgt (OneUnit p n N)) (s : OneLeafMixture p n N) : Prop where
  weight : (1/2:ℝ)≤s.amount w
  strength : oneLeafStrength s w m q.leafOld q.ζ q.e
  onTile : s.within (fun x=>w x≠0 ∧ (oneRawHoles m).unit (x true,x false) ∧
    oneFrameSide m x)

structure OneDurable (q : PreparationParameters) (l : Filter ℕ) (m : cycleM p)
    (w : OneTale p M) (s : OneRhythms p M) : Prop where
  mass : warm l (fun n=>(2*(M*n):ℕ)) (fun n=>(s n).amount (w n))
  shape : ∀ᶠ n in l,oneLeafStrength (s n) (w n) (m n) q.leafNew (2*q.ζ)
    (onePreparationPins q) ∧ (s n).within (oneFrameSide (m n))
  retained : ∃ c : ℝ,0<c ∧ ∀ᶠ n in l,c≤(s n).amount (w n)

def oneSeems (q : PreparationParameters) (m : Mixer p n) (s : OneLeafMixture p n N)
    (x : OneUnit p n N) (g : Bool→OneAugur p N) (z : Bool→Profile p n)
    (L : Bool→Finset (Label p.b)) (α : Party) (ε : ℝ):=
  (∀ i,(L i).card≤q.B ∧ z i∈oneEffectivePins (oneEndpointPrimalPins (s.rooting x)) i) ∧
    oneClaimed x g m z α L ε

def onePredicts (q : PreparationParameters) (m : Mixer p n) (s : OneLeafMixture p n N)
    (w : Wgt (OneUnit p n N)) (ε : ℝ):=
  ∃ g : Bool→OneAugur p N,(0.000001:ℝ)≤
    pr (s.sap w) (fun x=>∃ z L α,oneSeems q m s x g z L α ε)

def oneSecureAt (s : OneLeafMixture p n N):=
  oneSecurePin (fun x=>oneEndpointPrimalPins (s.rooting x))
    (fun x=>oneChannelPins (s.rooting x))

structure OneSketch (p : Shape) (M : ℕ) where
  c : PredictionClass
  α : Party
  r : F
  m : ∀ n,OneMarks p n (M*n)
  L : ∀ n,OneUnit p n (M*n)→Bool→Finset (Label p.b)
  g : Bool→OneSeason p M
  ε : ℕ→ℝ

def oneEngrave (b : OneSketch p M) (q : PreparationParameters) (m : cycleM p)
    (s : OneRhythms p M) (n : ℕ) (x : OneUnit p n (M*n)):=
  oneSeems q (m n) (s n) x (fun i=>b.g i n) (b.m n x) (b.L n x) b.α (b.ε n) ∧
    glint p (b.m n x)=b.r ∧ (b.c=dusk→ oneExactInk (m n) (b.m n) x)

structure OneLedger (b : OneSketch p M) (l : Filter ℕ) : Prop where
  small : slight l b.ε
  light : b.c.lit b.α

structure OneBright (q : PreparationParameters) (l : Filter ℕ) (m : cycleM p)
    (s : OneRhythms p M) (b : OneSketch p M) : Prop where
  forecasts : OneLedger b l
  engraved : ∀ᶠ n in l,(s n).within (oneEngrave b q m s n)

def oneMatchProg (b : OneSketch p M) (n : ℕ):=
  oneMatchUp (fun x=>oneMarkedDelta x (b.m n x)) b.α b.r b.c
def oneGlow (s : OneRhythms p M) (w : OneTale p M) (b : OneSketch p M) (n : ℕ):=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n))) (oneMatchProg b n)
def oneGleam (s : OneRhythms p M) (w : OneTale p M) (b : OneSketch p M) (n : ℕ):=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n)))
    (fun x=>oneMatchProg b n x ∧ ¬oneSecureAt (s n) x)
def oneGilded (s : OneRhythms p M) (w : OneTale p M) (b : OneSketch p M) (n : ℕ):=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n)))
    (fun x=>oneMatchProg b n x ∧ oneSecureAt (s n) x)

theorem one_gilding (s : OneRhythms p M) (w : OneTale p M) (b : OneSketch p M) (n : ℕ)
    (h : IsLaw ((s n).sap (w n))) :
    oneGlow s w b n-oneGleam s w b n≤oneGilded s w b n := by
  have hv:=(pairW_law h h).nz
  have hh : oneGlow s w b n≤oneGilded s w b n+oneGleam s w b n:=
    (pr_mono hv (fun x h=>show (oneMatchProg b n x ∧ oneSecureAt (s n) x) ∨
      (oneMatchProg b n x ∧ ¬oneSecureAt (s n) x) from by tauto)).trans (pr_or_le hv)
  linarith only [hh]

abbrev OneCompatibilityCode (q : PreparationParameters) (p : Shape) (n N : ℕ) :=
  PairCode (OneUnit p n N) (bp (3*(onePreparationCover q)*(2*N:ℝ)))

def oneCodedLeaves (q : PreparationParameters) (s : OneLeafMixture p n N)
    (R : OneUnit p n N × OneUnit p n N → Prop) :=
  ∃ code : OneCompatibilityCode q p n N,
    (∀ i∈s.T,∀ x∈i,∀ y∈i,code.label x=code.label y) ∧
    ∀ x y,inTiles s.T x → inTiles s.T y → (code.read (x,y) ↔ R (x,y))

def oneOutside (q : PreparationParameters) (p : Shape) (n N : ℕ):=
  ∀ E : OneUnit p n N×OneUnit p n N→Prop,named E (bp (3*(onePreparationCover q)*(2*N:ℝ)))→
    named (E∘Prod.swap) (bp (3*(onePreparationCover q)*(2*N:ℝ)))→
    ∀ w (s : OneLeafMixture p n N) (m : Mixer p n),
      (∀ x,imagePlanRank (s.rooting x)≤onePreparationPins q)→
      IsLaw w→ oneBySide w m (shine (2*N))→ carried w (oneFrameSide m)→
      pr (pairW w w) (fun x=>E x ∧ ¬oneSecureAt s x)≤
        0.0005*pr (pairW w w) E+edgeError (2*N)

theorem one_outside_calendar (q : PreparationParameters) (g : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀ p : Shape,p.g=g→p.h=h→
      ∀ᶠ M : ℕ in atTop,∀ᶠ n : ℕ in atTop,oneOutside q p n (M*n) := by
  filter_upwards [one_guard_calendar g (onePreparationPins q) (3*(onePreparationCover q)) 0.0005
    (by positivity) (by norm_num)] with h hh p hg hp
  filter_upwards [hh p hg hp] with M hm
  filter_upwards [hm] with n hn
  intro E hE hF w s m hK hw hs hx
  exact hn E hE hF w (fun x=>oneEndpointPrimalPins (s.rooting x))
    (fun x=>oneChannelPins (s.rooting x)) m
    (fun x i e=>(one_endpoint_primal_pin_dimension _ i e).trans
      ((image_plan_component_dimension _ e).trans (hK x)))
    (fun x i e=>(one_channel_pin_dimension _ i e).trans
      ((image_plan_component_dimension _ e).trans (hK x))) hw hs
    (fun x hn=>by by_contra h; exact hn (hx x h))

end
end Lax793645Proofs.Simplifications
