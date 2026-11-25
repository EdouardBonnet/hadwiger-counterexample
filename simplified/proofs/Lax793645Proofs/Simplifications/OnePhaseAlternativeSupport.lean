/- Adapts the phase-alternative selection from the vendored Apache-2.0
OpenAI PhaseAlternativeSupport module. All probability inputs below use
the actual one-frame law and symmetric offset records. -/
import Lax793645Proofs.Simplifications.OneAdaptiveRecordBounds
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PhaseAlternativeSupport

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ}

def oneSymCov {p : Shape} {N : ℕ} (C : SymCover p N) : Cov p N:=fun z=>C z.1
def oneSymCovered {p : Shape} {N : ℕ} (C : SymCover p N) (x : Ambient p N):=covered p (oneSymCov C) x

theorem one_sym_covered_spelled {p : Shape} {N r : ℕ} {S : SymCover p N}
    (X : SymAtlas p r S) (A : SymBatch X N) (T : SymCover p N) (he : symOffsetCover X≤T) :
    oneSymCovered T (symSpelled X A) := by
  apply (cover_mem ..).mpr
  intro e
  have h : ∀ V : Mat (Fin (symBreadth X e)) (Fin N),
      symSrc X e*V∈box (T e) ⊤ :=
    fun V=>(box_mem ..).mpr ⟨(col_follow ..).trans (he e),le_top⟩
  have h' (V : Mat (Fin N) (Fin (symBreadth X e))) :
      V*(symSrc X e)ᵀ∈box ⊤ (T e) := by
    rw [box_mem,transpose_mul,transpose_transpose]
    exact ⟨le_top,(col_follow ..).trans (he e)⟩
  change symSrc X e*(A e)ᵀ+A e*(symSrc X e)ᵀ+symEdgeCost X e∈_
  refine Submodule.add_mem _ (add_mem_sup (h _) (h' _)) (Submodule.mem_sup_left ?_)
  change symSrc X e*X.2.2 e*(symSrc X e)ᵀ∈box (T e) ⊤
  rw [Matrix.mul_assoc]
  exact h _

theorem one_by_side_halving {w : Wgt (OneUnit p n N)} (m : Mixer p n)
    {H : ℝ} (hw : ∀ x,0≤w x) (hh : ∀ i o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (P : OneUnit p n N→Prop) {c : ℝ} (hc : 0<c) (hp : c/2≤pr w P) :
    ∀ i o,mapW (onW w P) (fun x=>x i) o≤rhUp H c*oneRaw m N o := by
  intro i x
  refine (mapW_cap (on_mon hw (show 0<c/2 by linarith) hp) _ x).trans ?_
  unfold rhUp
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hh i x) (by positivity)

def oneTonalMix {p : Shape} {n N} (Δ : OneUnit p n N → Ambient p (2*N)) (w) :=
  ∀ S R,S ≠ 0 ∨ R ≠ 0 → |channelPitch Δ oneListens w S R|< 0.005
def oneTonalTiny {p : Shape} {n N} (Δ : OneUnit p n N → Ambient p (2*N)) (w : Wgt (OneUnit p n N)) (d : ℕ) :=
  ∃ S : SymCover p (2*N), oneCoverDimension S≤d ∧ (∀ x,w x≠0 → oneSymCovered S (Δ x)) ∧
    ∀ i : Bool,∀ R : Party, |channelPitch Δ oneListens w (unary i) R|≤bp (-0.24*(2*N))

theorem one_pitch_turn (Δ : OneUnit p n N → Ambient p (2*N)) (w S R) :
    channelPitch Δ oneListens w S R=channelPitch Δ oneListens w R S := by
  unfold channelPitch
  rw [pairW_avg,pairW_avg,avg_avg]
  refine avg_congr (fun x hx => avg_congr (fun y hy => ?_))
  exact congrArg wsign (add_comm _ _)

theorem one_tonal_left (Δ : OneUnit p n N → Ambient p (2*N)) (w)
    (h : ∀ S R,S≠0 → |channelPitch Δ oneListens w S R|<0.005) : oneTonalMix Δ w := by
  rintro S R (he|he)
  · exact h _ _ he
  rw [one_pitch_turn]; exact h _ _ he

theorem one_glimpse_sub (x : OneUnit p n N) (i : Bool) (C : SymCover p (2*N)) {q : Comp p.g→ℕ}
    (A : ImageTuple (Comp p.g) q (2*N)) (h : ∀ z,colSp (A z) ≤ C z) (hA : ∀ z,Injective (A z).mulVec)
    (hg : oneTupleGlimpse x i (t:=fun z => dim (C z)) (fun z => pack (C z))) :
    oneTupleGlimpse x i A := by
  classical
  intro z
  obtain ⟨X,hX⟩ := pull_cols (pack (C z)) (A z) (by rw [colSp_pack]; exact h z)
  have hI : Injective X.mulVec := by
    have ht := hA z
    rw [←hX] at ht
    intro a b h
    apply ht
    rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,h]
  rw [←hX,← Matrix.mul_assoc]; exact inj_comp_mat _ _ (hg z) hI

def onePreGlimpse (x : OneUnit p n N) (C : SymCover p (2*N)) :=
  ∀ i,oneTupleGlimpse x i (t:=fun z => dim (C z)) (fun z => pack (C z))

theorem one_cover_glimpse_bill {w : Wgt (OneUnit p n N)} (hv : SubLaw w) (m : Mixer p n)
    {L : ℝ} (h : ∀ i o,mapW w (fun x=>x i) o≤L*oneRaw m N o) (hL : 0 ≤ L)
    (C : SymCover p (2*N)) (d : ℕ) (hd : oneCoverDimension C≤d)
    (hN : Fintype.card (Row p n)+2*p.h+1≤N) :
    pr w (fun x => ¬onePreGlimpse x C) ≤ 2*oneGlimpseBill p d L := by
  classical
  let M : ImageTuple (Comp p.g) (fun z => dim (C z)) (2*N) := fun z => pack (C z)
  let P (i : Bool) := fun x : OneUnit p n N => ¬oneTupleGlimpse x i M
  have hp x : ¬onePreGlimpse x C → ∃ i,P i x := by
    intro h
    unfold onePreGlimpse at h; push Not at h; exact h
  have hh z : dim (C z) ≤ d :=
    (Finset.single_le_sum (fun z _ => Nat.zero_le (dim (C z))) (Finset.mem_univ z)).trans hd
  refine ((pr_mono hv.nz hp).trans (pr_exists_le hv.nz P)).trans ?_
  rw [Fintype.sum_bool,two_mul]
  exact add_le_add (one_tuple_glimpse_failure M (fun z=>pack_inj _) hh hv m true hL (h true) hN)
    (one_tuple_glimpse_failure M (fun z=>pack_inj _) hh hv m false hL (h false) hN)

namespace OneBazaar

variable {T : SymCover p (2*N)}
variable (s : OneBazaar p n r T)

set_option maxHeartbeats 600000 in
theorem cover_options (Δ : OneUnit p n N →Ambient p (2*N)) (w : Wgt (OneUnit p n N))
    (m : Mixer p n) {ε L H l : ℝ} (hw : IsLaw w) (h : s.opened Δ w)
    (hi : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),
      pr (oneUnitRaw m N) (imagePinAgree oneDualImages a)≤fee (2*N) ε (imagePlanRank a.sp))
    (hl : 0 ≤ L) (he₀ : 0< l) (he' : l≤1) (hL : ∀ i o,mapW w (fun x=>x i) o≤L*oneRaw m N o)
    (hH : 0 ≤ H) (hF : ∀ x,w x≤H*oneUnitRaw m N x)
    (hN : Fintype.card (Row p n)+2*p.h+1≤N)
    (ht : num (SymAtlas p r T) ≤ bp (0.002*(2*N)))
    (hd : oneSelectionPrice p r n N L ε) (hd' : oneSelectionPrice p r n N (rhUp L l) ε)
    (k d : ℕ) (hK : k≤d) (hQ : oneQuest p r k n N H ε)
    (hk : oneGlimpseBill p k L+bp (-0.1*(2*N))<l^(k+1))
    (hg : 2*oneGlimpseBill p d L≤l/2)
    (hψ : 5*l+bp (-0.24*(2*N))<0.005) :
    ∃ P : OneUnit p n N→Prop,
      l/2≤pr w P ∧ (oneTonalMix Δ (onW w P) ∨ oneTonalTiny Δ (onW w P) d) := by
  classical
  let bite (C : SymCover p (2*N)) := fun x => symOffsetCover (s.ix x) ≤ C
  by_cases hh : ∀ C,oneCoverDimension C≤d → pr w (bite C) ≤ l
  · refine ⟨fun _ => True,by rw [pr_true,hw.total]; linarith, Or.inl ?_⟩
    rw [onW_true w hw]; apply one_tonal_left Δ w
    intro S R hS
    obtain ⟨j,hj⟩ : ∃ i,S i=1 := by
      by_contra! he
      exact hS (funext fun i => (bit_cases (S i)).resolve_right (he i))
    have heq := s.calm_pitch h hw j R S m hl hL hN hi hd ht
    have hφ := s.frequent_sparse hw h S j hj k d hK l he₀ hh
      (fun A G Z => s.bids_bound S j A G Z hw.sub (bag_rate m hl hw.sub hL hN hi h hd G j))
      m hN hi hH hQ hF hl hL ht hk
    exact ((heq.trans (add_le_add_left hφ _))).trans_lt hψ
  push Not at hh
  obtain ⟨C,hC,hX⟩ := hh
  let P := fun x : OneUnit p n N => bite C x ∧ onePreGlimpse x C
  have hp : l/2≤pr w P := by
    have ht := one_cover_glimpse_bill hw.sub m hL hl C d hC hN
    have hh := pr_shield hw.nz (bite C) (fun x => onePreGlimpse x C)
    change _ ≤ pr w P at hh
    linarith only [hh,hg,ht,hX]
  let v := onW w P
  have hv : IsLaw v := on_law hw.nz (lt_of_lt_of_le (half_pos he₀) hp)
  have he x (h' : v x≠0) : symStandard (s.ix x) ∧ ∀ i, symCompFor (s.ix x)
      (s.bag (s.ix x) i x) (onePrimalImages x i) (Δ x) := h x (onW_ne h').2
  have ht' (x y : OneUnit p n N) (hx : v x≠0) (hy : v y≠0) (i) :
      oneTupleGlimpse y i (symSrc (s.ix x)) := by
    have hh := he x hx
    exact one_glimpse_sub y i C _ (onW_ne hx).1.1 hh.1.2.2.1 ((onW_ne hy).1.2 i)
  have hUp := one_by_side_halving m hw.nz hL P he₀ hp
  refine ⟨P,hp,Or.inr ⟨C,hC,fun x hx => ?_,fun i R => ?_⟩⟩
  · obtain h := ((he x hx).2 true).2
    rw [h]; exact one_sym_covered_spelled (s.ix x) _ C (onW_ne hx).1.1
  exact (s.single_pitch he hv i R m (by unfold rhUp; positivity) hUp hN hi hd' ht).2
    (fun x hx y hy => ht' x y hx hy i)

end OneBazaar
end
end Lax793645Proofs.Simplifications
