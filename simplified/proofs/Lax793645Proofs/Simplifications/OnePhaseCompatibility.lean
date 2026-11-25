import Lax793645Proofs.Simplifications.OnePhasePatterns
import Lax793645Proofs.Simplifications.OneCommonPredictions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PhaseClassCompatibility

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset PredictionClass
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneMatchUp (Δ : OneUnit p n N→Ambient p (2*N)) (α : Party) (r : F)
    (c : PredictionClass) (x : OneUnit p n N×OneUnit p n N) :=
  c.compatible α r (oneQuench Δ x)

def oneExactInk (m : Mixer p n) (marks : OneUnit p n N→Bool→Profile p n)
    (x : OneUnit p n N) := ∀ i,silent (oneYoke m x i (marks x i) 1)

theorem one_lone_image (x : OneUnit p n N) (i : Bool) (o : OneOrient p n N)
    (v : Profile p n) :
    joinPhase p (oneListens x) (unary i) (oneImageProfile o v)=
      oneFunctional (x i) (oneMomentEmbed o v) := by
  classical
  unfold joinPhase unary
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same,one_smul,one_image_profile_readout]
    have he : onSide (oneListens x) i=onePhaseCube (x i):=by cases i <;> rfl
    rw [he,one_phase_actual]
  · intro j _ hj; simp [hj]
  simp

theorem one_zero_delta (marks : OneUnit p n N→Bool→Profile p n) (x : OneUnit p n N)
    (h : oneMarkedDelta x (marks x)=0) :
    oneMomentEmbed (x true) (marks x true)=oneMomentEmbed (x false) (marks x false) := by
  have he : oneImageProfile (x true) (marks x true)=oneImageProfile (x false) (marks x false):=
    add_right_cancel (h.trans (char_two _).symm)
  rw [one_image_profile_readout,one_image_profile_readout] at he
  funext e
  exact quadratic_moment_injective _ (oneAmbientCoordinates N).injective (congrFun he e)

theorem one_exact_inner (m : Mixer p n) (marks : OneUnit p n N→Bool→Profile p n)
    (x : OneUnit p n N) (h : oneExactInk m marks x) :
    ∀ i,∀ v∈Xspace p n,oneInner x i v=grad m (marks x i) v := by
  intro i v hv
  have he:=h i v hv
  change oneInner x i v+(Tsym m (marks x i) v+1*role p n v)=0 at he
  rw [one_mul,add_comm (Tsym m (marks x i) v),←grad_val] at he
  exact add_right_cancel (he.trans (char_two _).symm)

theorem one_delta_dusk (m : Mixer p n) (marks : OneUnit p n N→Bool→Profile p n)
    (x : OneUnit p n N) (hx : ∀ i,marks x i∈Xspace p n)
    (h : oneExactInk m marks x) (hz : oneMarkedDelta x (marks x)=0)
    (he : (oneRawHoles m).unit (x true,x false)) (hi : ∀ i,oneFrameLaw m (x i)) :
    glint p (marks x)=0 := by
  apply (bit_cases _).resolve_right
  intro hh
  have heq:=one_exact_inner m marks x h
  unfold glint at hh
  rw [Fintype.sum_bool] at hh
  apply he
  exact ⟨hi true,hi false,marks x true,marks x false,hx _,hx _,one_zero_delta marks x hz,
    heq true,heq false,hh⟩

/-- Each inactive endpoint listener annihilates its own unit's offset. -/
theorem one_diag_dusk_endpoint (m : Mixer p n) (marks : OneUnit p n N→Bool→Profile p n)
    (x : OneUnit p n N) (hx : ∀ i,marks x i∈Xspace p n)
    (h : oneExactInk m marks x) (hi : ∀ i,oneFrameLaw m (x i)) (i : Bool) :
    joinPhase p (oneListens x) (unary i) (oneMarkedDelta x (marks x))=0 := by
  have he (j) : oneInner x j (marks x j)=0 := by
    rw [one_exact_inner m marks x h _ _ (hx j),grad_val,T_diag,char_two]
  have h₁ : oneFunctional (x true) (oneMomentEmbed (x false) (marks x false))=0:=he false
  have h₂ : oneFunctional (x false) (oneMomentEmbed (x true) (marks x true))=0:=he true
  cases i <;> simp only [oneMarkedDelta,map_add,one_lone_image,one_functional_self (hi _),h₁,h₂,add_zero]

theorem one_diag_dusk (m : Mixer p n) (marks : OneUnit p n N→Bool→Profile p n)
    (x : OneUnit p n N) (hx : ∀ i,marks x i∈Xspace p n)
    (h : oneExactInk m marks x) (hi : ∀ i,oneFrameLaw m (x i)) :
    joinPhase p (oneListens x) allSide (oneMarkedDelta x (marks x))=0 := by
  rw [one_tone_vec,dotProduct,Fintype.sum_bool]
  simp only [allSide,one_mul,one_diag_dusk_endpoint m marks x hx h hi,add_zero]

theorem one_fade (c : PredictionClass) (α : Party) (r : F)
    (h : c.lit α) (hα : α true=α false) (hd : c=dusk → r=0)
    (Δ : OneUnit p n N→Ambient p (2*N)) (x : OneUnit p n N × OneUnit p n N)
    (hx : Δ x.1=0) (hy : Δ x.2=0) :
    oneMatchUp Δ α r c x := by
  classical
  have ht : oneQuench Δ x=0 := by
    unfold oneQuench; rw [hx,hy]
    simp only [map_zero]; rfl
  unfold oneMatchUp; rw [ht]
  cases c
  · rw [hd rfl]; rfl
  · rename_i i
    cases i
    · have hh : firstBit α true=0 := h.1 true (show false≠true from Bool.false_ne_true)
      unfold firstBit at hh; rw [hα] at hh
      exact (zero_add _).trans hh.symm
    have hh : firstBit α false=0 := h.1 false (show true≠false from Ne.symm Bool.false_ne_true)
    unfold firstBit at hh; rw [←hα] at hh
    exact (zero_add _).trans hh.symm
  · simp [compatible]
  trivial

/-- One scalar character bound controls either prescribed singleton parity. -/
theorem one_singleton_bias_mass (p : Shape) {n N : ℕ} (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) (α r i)
    (hi : |channelPitch Δ oneListens w (unary i) (unary i)| ≤0.1) :
    0.4 ≤ pr (pairW w w) (oneMatchUp Δ α r (dawn i)) := by
  classical
  let P := oneMatchUp Δ α r (dawn i)
  let v := firstBit α i
  let x (x : OneUnit p n N×OneUnit p n N) :=
    joinPhase p (oneListens x.1) (unary i) (Δ x.2)+joinPhase p (oneListens x.2) (unary i) (Δ x.1)
  let C:=pairW w w
  have he (j) : P j ↔ x j = v := by
    unfold P oneMatchUp compatible oneQuench x v; simp only [add_comm]
  have hU : pr C P=(1/2)*(avg C (fun _=>1)+wsign v * avg C (fun i=> wsign (x i))) := by
    unfold pr
    rw [←avg_mul',←avg_add,←avg_mul']
    apply avg_congr
    intro i _
    rcases bit_cases v with h|h<;> rcases bit_cases (x i) with hx|hx <;> norm_num [he,h,hx,ind]
  have hz := abs_le.mp hi
  change |avg C (fun i=> wsign (x i))| ≤_ at hi
  change _≤pr C P
  rw [hU,(pairW_law hw hw).avg_const]
  rcases bit_cases v with h|h <;> rw [h] <;> simp only [wsign_zero, wsign_one,one_mul,neg_mul] <;>
    linarith only [(abs_le.mp hi).1,(abs_le.mp hi).2]

theorem one_tiny_morn (p : Shape) {n N : ℕ} (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) (d : ℕ) (h : oneTonalTiny Δ w d)
    (hN : bp (-0.24*(2*N)) < 0.1) (α r i) :
    0.4 ≤ pr (pairW w w) (oneMatchUp Δ α r (dawn i)) := by
  obtain ⟨_,_,_,hx⟩:=h
  exact one_singleton_bias_mass p Δ w hw α r i ((hx i _).trans hN.le)
end
end Lax793645Proofs.Simplifications
