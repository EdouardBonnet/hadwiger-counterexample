import Lax793645Proofs.Simplifications.OneMarginalPhaseBounds
import Lax793645Proofs.Simplifications.OnePhaseMomentBounds
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.OffsetFourierBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N r : ℕ} {T : SymCover p (2*N)}

def onePrimalImages (x : OneUnit p n N) (i : Bool) : SymCover p (2*N):=
  fun e=>colSp (onePrimalMatrix (x i e))

structure OneBazaar (p : Shape) {N : ℕ} (n r : ℕ) (T : SymCover p (2*N)) where
  ix : OneUnit p n N→SymAtlas p r T
  bag : (M : SymAtlas p r T)→Bool→OneUnit p n N→SymBatch M (2*N)

namespace OneBazaar

variable (s : OneBazaar p n r T)

def opened (Δ : OneUnit p n N→Ambient p (2*N)) (w : Wgt (OneUnit p n N)) : Prop:=
  ∀ x,w x≠0→symStandard (s.ix x) ∧∀ i,
    symCompFor (s.ix x) (s.bag (s.ix x) i x) (onePrimalImages x i) (Δ x)

def chart (w : Wgt (OneUnit p n N)) (M : SymAtlas p r T):=subW w (fun x=>s.ix x=M)

theorem active {Δ : OneUnit p n N→Ambient p (2*N)} {w : Wgt (OneUnit p n N)}
    {M : SymAtlas p r T} (h : s.opened Δ w) (x : OneUnit p n N) (hx : s.chart w M x≠0) :
    s.ix x=M ∧symStandard M ∧∀ i,symCompFor M (s.bag M i x) (onePrimalImages x i) (Δ x) := by
  have he : s.ix x=M:=Classical.byContradiction (fun he=>hx (subW_carried w _ _ he))
  refine ⟨he,?_⟩
  subst M
  exact h x (left_ne_zero_of_mul hx)

def pay (M G : SymAtlas p r T) (i : Bool) (S : Party) (y : OneUnit p n N) :
    SymBatch M (2*N)×SymBatch G (2*N):=(oneThermal y S (symSrc M),s.bag G i y)

end OneBazaar

def oneSelectionPrice (p : Shape) (r n N : ℕ) (H ζ : ℝ) : Prop:=
  ∀ q t : ℕ,q≤r→t≤r→H*oneHeatRate p n N ζ q t≤loseA p (2*N) q t

namespace OneBazaar
variable {s : OneBazaar p n r T}

theorem bag_rate (m : Mixer p n) {H ζ : ℝ} (hH : 0≤H)
    {w : Wgt (OneUnit p n N)} {Δ : OneUnit p n N→Ambient p (2*N)}
    (hw : SubLaw w) (hside : ∀ i o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (hcap : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ζ (imagePlanRank a.sp))
    (hopen : s.opened Δ w) (hp : oneSelectionPrice p r n N H ζ)
    (M : SymAtlas p r T) (i : Bool) :
    ∀ z,mapW (s.chart w M) (s.bag M i) z≤loseA p (2*N) (symCells M) 0 := by
  intro z
  have hv:=subLaw_sub hw (fun x=>s.ix x=M)
  by_cases hM : symStandard M
  · refine (pr_on_mono hv.nz (Q:=fun x=>oneBasisFrom x i z) ?_).trans ?_
    · intro x hx he
      subst z
      exact ((s.active hopen x hx).2.2 i).1
    apply (pr_mono_left (subW_le hw.nz _) _).trans
    exact (one_heat_none i z hH m hroom hcap (hside i)).trans (hp _ 0 hM.2.1 (Nat.zero_le _))
  have hz : s.chart w M=(fun _=>0):=funext (fun x=>Classical.byContradiction
    (fun hx=>hM (s.active hopen x hx).2.1))
  rw [hz]
  simp only [mapW,pr,avg,zero_mul,Finset.sum_const_zero]
  exact (bp_pos _).le

theorem glimpse_prize (m : Mixer p n) {H ζ : ℝ} (hH : 0≤H)
    {w : Wgt (OneUnit p n N)} {Δ : OneUnit p n N→Ambient p (2*N)}
    (hw : SubLaw w) (hside : ∀ i o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (hcap : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ζ (imagePlanRank a.sp))
    (hopen : s.opened Δ w) (hp : oneSelectionPrice p r n N H ζ)
    (M G : SymAtlas p r T) (i : Bool) (hM : symStandard M) (hG : symStandard G)
    (P : OneUnit p n N→Prop)
    (hP : ∀ x,s.chart w G x≠0→P x → oneTupleGlimpse x i (symSrc M)) :
    ∀ z,mapW (subW (s.chart w G) P) (s.pay M G i (unary i)) z≤prize p (2*N) (symCells G) := by
  rintro ⟨A,Z⟩
  have hv:=subLaw_sub hw (fun x=>s.ix x=G)
  change pr (subW (s.chart w G) P) _≤_
  rw [pr_sub]
  refine (pr_on_mono hv.nz (Q:=fun x=>oneBasisFrom x i Z ∧
    oneTupleGlimpse x i (symSrc M) ∧oneThermal x (unary i) (symSrc M)=A) ?_).trans ?_
  · rintro x hx ⟨h,hz⟩
    have he : s.bag G i x=Z:=congrArg Prod.snd hz
    exact ⟨he ▸ ((s.active hopen x hx).2.2 i).1,hP x hx h,congrArg Prod.fst hz⟩
  apply (pr_mono_left (subW_le hw.nz _) _).trans
  apply (one_heat_one i (symSrc M) A Z hH m hroom hcap (hside i)).trans
  apply (hp (symCells G) (symCells M) hG.2.1 hM.2.1).trans
  unfold loseA prize
  apply bp_le
  have ht : (1:ℝ)≤symCells M:=by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM.1
  push_cast
  nlinarith [(Nat.cast_nonneg N : (0:ℝ)≤N)]

end OneBazaar
end
end Lax793645Proofs.Simplifications
