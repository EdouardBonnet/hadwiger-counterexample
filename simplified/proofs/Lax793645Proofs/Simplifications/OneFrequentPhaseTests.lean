/- Adapts the finite frequency-list argument from the vendored Apache-2.0
OpenAI SingletonPhaseTests module to the one-frame law. -/
import Lax793645Proofs.Simplifications.OneSingletonPhaseTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {T : SymCover p (2*N)}
namespace OneBazaar
variable (s : OneBazaar p n r T)

def frequent (w : Wgt (OneUnit p n N)) (S : Party) (j : Bool)
    (M G : SymAtlas p r T) (y : OneUnit p n N) :=
  prize p (2*N) (symCells G) < mapW (s.chart w G) (s.pay M G j S) (s.pay M G j S y)

theorem calm_pitch {w : Wgt (OneUnit p n N)} {Δ}
    (hl : s.opened Δ w) (hv : IsLaw w) (i : Bool) (R S : Party)
    (m : Mixer p n) {H ζ : ℝ} (hH : 0≤H)
    (hw : ∀ i o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (hcap : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ζ (imagePlanRank a.sp))
    (hp : oneSelectionPrice p r n N H ζ) (ht : num (SymAtlas p r T)≤bp (0.002*(2*N))) :
    |channelPitch Δ oneListens w S R| ≤ pr (pairW w w)
      (fun x => s.frequent w S i (s.ix x.1) (s.ix x.2) x.2) + bp (-0.24*(2*N)) := by
  classical
  let C : OneSales p n r T := fun M G y => ¬ s.frequent w S i M G y
  have hb (M G : SymAtlas p r T) (hh : symStandard M) (hh' : symStandard G) :
      ∀ y,mapW (subW (s.chart w G) (C M G)) (s.pay M G i S) y ≤ prize p (2*N) (symCells G) := by
    let v := s.chart w G
    let J := s.pay M G i S
    have hw' : SubLaw v := subLaw_sub hv.sub _
    intro y
    by_cases he : mapW v J y≤prize p (2*N) (symCells G)
    · exact (pr_mono_left (subW_le hw'.nz _) _).trans he
    change pr (subW v (C M G)) (fun x => J x=y) ≤ _
    rw [pr_sub]
    have hx : (fun x => C M G x ∧ J x=y)=(fun _ => False) := by
      funext x
      refine propext (iff_false_intro (fun ⟨h,h'⟩ => he ?_))
      rw [← h']
      exact le_of_not_gt h
    rw [hx,pr_false]; exact (bp_pos _).le
  have hf := beat_mix s hl hv S R i C (fun M => bag_rate m hH hv.sub hw hroom hcap hl hp M i) hb ht
  unfold discard C at hf; simpa only [not_not] using hf

/-- fixed companion Z restrict frequent pair to this list of small Φ values -/
def bids (w : Wgt (OneUnit p n N)) (S : Party) (i : Bool)
    (M G : SymAtlas p r T) (Z : SymBatch G (2*N)) : Finset (SymBatch M (2*N)) :=
  open scoped Classical in
  Finset.univ.filter (fun x => prize p (2*N) (symCells G)<mapW (s.chart w G) (s.pay M G i S) (x,Z))

theorem bids_mem (w : Wgt (OneUnit p n N)) (S : Party) (i : Bool)
    (M G : SymAtlas p r T) (x : OneUnit p n N) :
    s.frequent w S i M G x ↔
      oneThermal x S (symSrc M) ∈ s.bids w S i M G (s.bag G i x) := by
  classical
  simp only [bids,Finset.mem_filter,Finset.mem_univ,true_and]
  rfl

theorem bids_bound {w : Wgt (OneUnit p n N)} (S : Party) (i : Bool)
    (M G : SymAtlas p r T) (Z : SymBatch G (2*N)) (hw : SubLaw w)
    (h : ∀ x,mapW (s.chart w G) (s.bag G i) x ≤ loseA p (2*N) (symCells G) 0) :
    (↑(s.bids w S i M G Z).card:ℝ) ≤ bp (0.51*(2*N)) := by
  classical
  let f := s.pay M G i S
  let v := s.chart w G
  have hv : SubLaw v := subLaw_sub hw _
  let B := s.bids w S i M G Z
  let P := prize p (2*N) (symCells G)
  have he (x) (hx : x∈B) : P≤mapW v f (x,Z) := (Finset.mem_filter.mp hx).2.le
  have hg : ↑B.card * P ≤ loseA p (2*N) (symCells G) 0 := by
    have hZ : ∑ x : SymBatch M (2*N),mapW v f (x,Z)=mapW v (s.bag G i) Z := by
      let T := fun x => (f x).1
      have hh (x : SymBatch M (2*N)) : (fun y => f y=(x,Z))=
          fun y => s.bag G i y=Z ∧ T y=x := by ext y; simp [Prod.mk.injEq,f,T,pay,and_comm]
      simp only [mapW,hh,sum_pr_tag]
    calc ↑B.card * P = ∑ x ∈ B,P := (by simp)
         _ ≤ ∑ x∈B,mapW v f (x,Z) := Finset.sum_le_sum he
         _ ≤ ∑ x : SymBatch M (2*N),mapW v f (x,Z) := Finset.sum_le_sum_of_subset_of_nonneg
           (Finset.subset_univ B) (fun i _ _ => pr_nonneg hv.nz)
         _ ≤ loseA p (2*N) (symCells G) 0 := hZ.trans_le (h Z)
  refine (le_of_mul_le_mul_right (hg.trans_eq ?_) (bp_pos _ : 0<P))
  unfold P prize loseA
  rw [← bp_add]; congr 1; push_cast; ring

end OneBazaar
end
end Lax793645Proofs.Simplifications
