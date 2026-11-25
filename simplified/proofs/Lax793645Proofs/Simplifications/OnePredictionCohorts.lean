/- Finite witness selection adapted from the vendored Apache-2.0
PredictionDichotomy proof, for the quadratic-frame law and closed pins. -/
import Lax793645Proofs.Simplifications.OnePreparationConditions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PredictionDichotomy

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open PreparationParameters PredictionClass Filter Finset Matrix
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {q : PreparationParameters}

structure OneSage (p : Shape) (n N : ℕ) where
  g : Bool→OneAugur p N
  m : OneMarks p n N
  L : OneUnit p n N → Bool→ Finset (Label p.b)

instance : Inhabited (OneSage p n N) := ⟨⟨fun _ _ _ _=>0,fun _=>0,fun _ _=>∅⟩⟩

abbrev OneBanners := Party × F × Bool

def oneTender {p : Shape} {n N} (i : OneSage p n N) (q : PreparationParameters) (m : Mixer p n)
    (s : OneLeafMixture p n N) (z : OneBanners) (ε : ℝ) (x : OneUnit p n N) :=
  oneSeems q m s x i.g (i.m x) (i.L x) z.1 ε ∧ glint p (i.m x)=z.2.1 ∧
    ((z.2.2=true) ↔ oneMarkedDelta x (i.m x)=0)

set_option maxHeartbeats 1200000 in
theorem one_cohort_threshold (m : Mixer p n) (w : Wgt (OneUnit p n N)) (s : OneLeafMixture p n N)
    (hs : OneEntered q m w s) (hw : IsLaw w) {ε : ℝ}
    (seed : ℝ) (hseed : (Fintype.card OneBanners:ℝ)*seed<0.000001)
    (Inv : (Bool→OneAugur p N)→Prop)
    (h : ∃ g : Bool→OneAugur p N,Inv g ∧
      (0.000001:ℝ)≤pr (s.sap w) (fun x=>∃ z L α,oneSeems q m s x g z L α ε)) :
    ∃ (z : OneBanners) (i : OneSage p n N), Inv i.g ∧ (∀ x j,totalRank (i.m x j)≤q.e) ∧
      seed ≤ pr (s.sap w) (oneTender i q m s z ε) := by
  classical
  let v:=s.sap w
  have hv := ImageLeafMixture.sap_law (lt_of_lt_of_le (by norm_num) hs.weight) hw
  obtain ⟨g,hInv,hg⟩:=h
  let P (x : OneUnit p n N) := ∃ z L α, oneSeems q m s x g z L α ε
  let Q x:= v x≠ 0∧P x
  have ht : pr v Q=pr v P := avg_congr fun x h=> (by change ind (v x≠0∧P x)=ind (P x); rw [show (v x≠0∧P x)=(P x) from propext (and_iff_right h)])
  choose f hf using show
    ∀ x : OneUnit p n N,∃ (z : Bool→Profile p n) (L : Bool→Finset (Label p.b))
      (α : Party), (∀ j,totalRank (z j)≤ q.e) ∧ (Q x → oneSeems q m s x g z L α ε) from by
    intro x; by_cases h : Q x
    · obtain ⟨z,L,a,hv⟩:=h.2
      refine ⟨z,L,a,fun i=>?_,fun _=>hv⟩
      exact (one_effective_rank _ i _ (hv.1 i).2).trans (ImageLeafMixture.root_bound hs.strength _)
    refine ⟨0,fun _=>∅,0,fun i=>?_,fun he=>(h he).elim⟩
    unfold totalRank
    have hh (j:Comp p.g) :
        ((0:Profile p n) j).rank=0 := Matrix.rank_zero
    exact le_trans (Finset.sum_eq_zero (fun i _=>hh i)).le (Nat.zero_le _)
  choose L a hA hh using hf
  let i:= (⟨g,f,L⟩: OneSage p n N)
  have he x (h : Q x) : ∃ z : OneBanners,oneTender i q m s z ε x := by
    refine ⟨(a x,glint p (i.m x),decide (oneMarkedDelta x (i.m x)=0)),hh x h,rfl,?_⟩
    simp
  have ht' : (0.000001:ℝ) ≤ ∑ j : OneBanners,pr v (oneTender i q m s j ε) :=
    hg.trans ((ht.symm ▸ pr_mono hv.nz he).trans (pr_exists_le hv.nz _))
  have hz : ∃ j : OneBanners,seed ≤ pr v (oneTender i q m s j ε) := by
    by_contra! h
    have hx : 0.000001≤∑ _j : OneBanners,seed :=
      ht'.trans (Finset.sum_le_sum fun j _=>(h j).le)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hx
    exact hseed.not_ge hx
  obtain ⟨j,hj⟩:=hz
  exact ⟨j,i,hInv,hA,hj⟩

theorem one_cohort_preserving (m : Mixer p n) (w : Wgt (OneUnit p n N)) (s : OneLeafMixture p n N)
    (hs : OneEntered q m w s) (hw : IsLaw w) {ε : ℝ}
    (Inv : (Bool→OneAugur p N)→Prop)
    (h : ∃ g : Bool→OneAugur p N,Inv g ∧
      (0.000001:ℝ)≤pr (s.sap w) (fun x=>∃ z L α,oneSeems q m s x g z L α ε)) :
    ∃ (z : OneBanners) (i : OneSage p n N),Inv i.g ∧ (∀ x j,totalRank (i.m x j)≤q.e) ∧
      crowdSeed≤pr (s.sap w) (oneTender i q m s z ε) :=
  one_cohort_threshold m w s hs hw crowdSeed (by
    norm_num [OneBanners,Party,F,Vec,ZMod.card,crowdSeed,pollen]) Inv h

theorem one_cohort_reserve (m : Mixer p n) (w : Wgt (OneUnit p n N)) (s : OneLeafMixture p n N)
    (hs : OneEntered q m w s) (hw : IsLaw w) {ε : ℝ}
    (Inv : (Bool→OneAugur p N)→Prop)
    (h : ∃ g : Bool→OneAugur p N,Inv g ∧
      (0.000001:ℝ)≤pr (s.sap w) (fun x=>∃ z L α,oneSeems q m s x g z L α ε)) :
    ∃ (z : OneBanners) (i : OneSage p n N),Inv i.g ∧ (∀ x j,totalRank (i.m x j)≤q.e) ∧
      4*crowdSeed≤pr (s.sap w) (oneTender i q m s z ε) :=
  one_cohort_threshold m w s hs hw (4*crowdSeed) (by
    norm_num [OneBanners,Party,F,Vec,ZMod.card,crowdSeed,pollen]) Inv h

end
end Lax793645Proofs.Simplifications
