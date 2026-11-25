/-
Adapts the finite chart and Walsh assembly from the vendored Apache-2.0
OpenAI OffsetFourierBounds module to symmetric one-frame offsets.
-/
import Lax793645Proofs.Simplifications.OneSupportedPhaseLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {T : SymCover p (2*N)}

def oneChant (Δ : OneUnit p n N→Ambient p (2*N)) (S R : Party) :
    Wgt (OneUnit p n N×OneUnit p n N):=
  fun x=>wsign (joinPhase p (oneListens x.1) R (Δ x.2)+joinPhase p (oneListens x.2) S (Δ x.1))

theorem image_tuple_pair_comm {C : Type} [Fintype C] (r : C→ℕ) (N : ℕ)
    (x y : ImageTuple C r N) : imageTuplePair r N x y=imageTuplePair r N y x := by
  rw [image_tuple_pair_apply,image_tuple_pair_apply]
  exact Finset.sum_congr rfl (fun _ _=>mpair_comm ..)

namespace OneBazaar
variable (s : OneBazaar p n r T)

abbrev OneSales (p : Shape) {N : ℕ} (n r : ℕ) (T : SymCover p (2*N)) :=
  SymAtlas p r T → SymAtlas p r T → OneUnit p n N → Prop

def discard {s : OneBazaar p n r T} (w : Wgt (OneUnit p n N)) (C : OneSales p n r T) :=
  pr (pairW w w) (fun x => ¬ C (s.ix x.1) (s.ix x.2) x.2)

set_option maxHeartbeats 800000 in
private theorem beat_one {w : Wgt (OneUnit p n N)} {Δ}
    (hl : s.opened Δ w) (hv : SubLaw w) (M G : SymAtlas p r T)
    (S R : Party) (i : Bool) (C : OneUnit p n N → Prop)
    (hA : ∀ x,mapW (s.chart w M) (s.bag M i) x ≤ loseA p (2*N) (symCells M) 0)
    (hB : symStandard M → symStandard G → ∀ y,mapW (subW (s.chart w G) C)
      (s.pay M G i S) y ≤ prize p (2*N) (symCells G)) :
    |avg (pairW (s.chart w M) (subW (s.chart w G) C)) (oneChant Δ S R)| ≤ beat (2*N) := by
  classical
  let u := s.chart w M
  let v := subW (s.chart w G) C
  have hw : SubLaw u := subLaw_sub hv _
  have ht : SubLaw v := subLaw_sub (subLaw_sub hv _) _
  let y := avg (pairW u v) (oneChant Δ S R)
  by_cases hy : y=0
  · change |y|≤_
    rw [hy, abs_zero]; exact (bp_pos _).le
  have h : ∃ x,pairW u v x ≠ 0 := by
    by_contra! he
    apply hy; unfold y avg; simp_rw [he]; simp
  obtain ⟨⟨x0,y0⟩,hx⟩ := h
  have hV x (hh : v x≠0) : s.chart w G x≠0 := left_ne_zero_of_mul hh
  have H (x : OneUnit p n N) (hh : u x≠0) := s.active hl x hh
  have H' (x : OneUnit p n N) (hh : v x≠0) := s.active hl x (hV x hh)
  let a (x) := (s.bag M i x,oneThermal x R (symSrc G))
  let b := s.pay M G i S
  let f (x : OneUnit p n N) := wsign (joinPhase p (oneListens x) R (symEdgeCost G))
  let g (x : OneUnit p n N) := wsign (joinPhase p (oneListens x) S (symEdgeCost M))
  let B := coupledB (imageTuplePair (symBreadth M) (2*N)) (imageTuplePair (symBreadth G) (2*N))
  have hc :
      y=avg (pairW u v) (fun x => f x.1*g x.2*wsign (B (a x.1) (b x.2))) := by
    refine avg_congr fun ⟨x,y⟩ hh => ?_
    have h1 := ((H x (left_ne_zero_of_mul hh)).2.2 i).2
    have h2 := ((H' y (right_ne_zero_of_mul hh)).2.2 i).2
    unfold oneChant; dsimp only
    rw [h1,h2,one_tone_symmetric_offset,one_tone_symmetric_offset]
    unfold f g
    rw [←wsign_add,←wsign_add]
    apply congrArg wsign
    change _=_+(imageTuplePair (symBreadth M) (2*N) _ _+imageTuplePair (symBreadth G) (2*N) _ _)
    rw [image_tuple_pair_comm (symBreadth G) (2*N) (s.bag G i y)]
    dsimp only [coupledB,b,pay,a]
    simp only [LinearMap.fst_apply,LinearMap.snd_apply]
    abel
  let D := SymBatch M (2*N) × SymBatch G (2*N)
  have ha (x : D) : mapW u a x ≤ loseA p (2*N) (symCells M) 0 := by
    refine (pr_mono hw.nz (p:=fun y => a y=x) (q:=fun y => s.bag M i y=x.1)
      (fun y h => ?_)).trans (hA x.1)
    exact congrArg Prod.fst h
  have hb (x : D) : mapW v b x ≤ prize p (2*N) (symCells G) :=
    hB ((H x0 (left_ne_zero_of_mul hx)).2.1) ((H' y0 (right_ne_zero_of_mul hx)).2.1) x
  have he := walsh_weighted B
    (coupledB_inj (image_tuple_pair_inj ..) (image_tuple_pair_inj ..)) u v hw ht a b f g (fun x => by simp [f])
    (fun x => by simp [g]) ha hb
  have hi : y^2 ≤ beat (2*N)^2 := by
    rw [hc]
    refine he.trans ?_
    let F := SymBatch M (2*N)
    let G' := SymBatch G (2*N)
    unfold num
    rw [card_space,dim,finrank_prod]
    have hf : finrank Lax793645Proofs.Upstream.OAI.HadwigerCounterexample.F F=(2*N)*symCells M := image_tuple_dimension _ _
    have hg : finrank Lax793645Proofs.Upstream.OAI.HadwigerCounterexample.F G'=(2*N)*symCells G := image_tuple_dimension _ _
    rw [hf,hg,loseA,prize,beat,←bp_add,←bp_add,pow_two,←bp_add]
    apply le_of_eq; push_cast; ring_nf
  change |y|≤_
  exact le_of_pow_le_pow_left₀ (show 2 ≠ (0:ℕ) by decide) (bp_pos _).le
    (sq_abs y ▸ hi)

set_option maxHeartbeats 800000 in
theorem beat_mix {w : Wgt (OneUnit p n N)} {Δ}
    (hl : s.opened Δ w) (hv : IsLaw w) (S R : Party) (i : Bool) (C : OneSales p n r T)
    (hA : ∀ M x,mapW (s.chart w M) (s.bag M i) x ≤ loseA p (2*N) (symCells M) 0)
    (hB : ∀ M G,symStandard M → symStandard G → ∀ y,mapW (subW (s.chart w G) (C M G))
      (s.pay M G i S) y ≤ prize p (2*N) (symCells G))
    (ht : num (SymAtlas p r T) ≤ bp (0.002*(2*N))) :
    |channelPitch Δ oneListens w S R| ≤ discard (s:=s) w C + bp (-0.24*(2*N)) := by
  classical
  let V := pairW w w
  let F := oneChant Δ S R
  let P := fun x : (OneUnit p n N)×_ => C (s.ix x.1) (s.ix x.2) x.2
  let g := fun x => ind (P x)*F x
  let f := fun x => ind (¬P x)*F x
  let μ := s.chart w
  let W := fun M G => subW (μ G) (C M G)
  have hn x : 0≤ V x := (pairW_law hv hv).nz x
  have he x : F x=f x+ g x := by
    unfold f g
    by_cases h : P x <;> simp [h]
  have hf : |avg V f| ≤ discard (s:=s) w C := by
    refine (abs_avg_le hn).trans_eq ?_
    unfold discard pr
    refine avg_congr (fun x _ => ?_)
    rw [show f x= _*_ from rfl, abs_mul, abs_of_nonneg (ind_nonneg (¬P x))]
    simp [F,P,oneChant]
  have hg :
      avg V g=∑ M : SymAtlas p r T,∑ G : SymAtlas p r T, avg (pairW (μ M) (W M G)) F := by
    let U (M G : SymAtlas p r T) (x : OneUnit p n N × OneUnit p n N) :=
      ind (s.ix x.1=M)*ind (s.ix x.2=G)*ind (C M G x.2)*F x
    have hu (M G : SymAtlas p r T) :
        avg (pairW (μ M) (W M G)) F=avg V (U M G) := by
      unfold avg
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold U W μ V pairW chart subW; ring
    simp_rw [hu,← avg_sum]
    refine avg_congr fun x _ => ?_
    rw [Finset.sum_eq_single (s.ix x.1)]
    · rw [Finset.sum_eq_single (s.ix x.2)]
      · simp only [U,ind_true,one_mul]; rfl
      · intro j _ hj; simp [U,ind_zero hj.symm]
      simp
    · intro j _ hj; simp [U,ind_zero hj.symm]
    simp
  have hh : |avg V g| ≤ bp (-0.24*(2*N)) := by
    rw [hg]; apply le_trans (Finset.abs_sum_le_sum_abs ..)
    let J := num (SymAtlas p r T)
    have hz (M : SymAtlas p r T) :
        |∑ G : SymAtlas p r T, avg (pairW (μ M) (W M G)) F|≤ J*beat (2*N) := by
      refine (Finset.abs_sum_le_sum_abs ..).trans
        ((Finset.sum_le_sum (fun i' _ =>
          beat_one s hl hv.sub M i' S R i (C M i') (hA M) (hB M i'))).trans_eq ?_)
      simp only [J,Finset.sum_const, Finset.card_univ,nsmul_eq_mul,num]
    calc ∑ M : SymAtlas p r T,|∑ G : SymAtlas p r T,avg (pairW (μ M) (W M G)) F|
      _ ≤ ∑ _ : SymAtlas p r T,J*beat (2*N) := Finset.sum_le_sum fun M _ => hz M
      _ = J*J*beat (2*N) := by simp [J,mul_assoc,num]
      _ ≤ bp (0.002*(2*N))*bp (0.002*(2*N))*beat (2*N) := mul_le_mul_of_nonneg_right
        (mul_self_le_mul_self (Nat.cast_nonneg _ : 0≤J) ht) (bp_pos _).le
      _ ≤ bp (-0.24*(2*N)) := by
        unfold beat
        rw [←bp_add,←bp_add]
        apply bp_le
        push_cast
        linarith [(Nat.cast_nonneg N : (0:ℝ)≤N)]
  change |avg V F|≤ _
  rw [show F=(fun x => f x+g x) from funext he,avg_add]
  exact (abs_add_le ..).trans (add_le_add hf hh)

end OneBazaar

end
end Lax793645Proofs.Simplifications
