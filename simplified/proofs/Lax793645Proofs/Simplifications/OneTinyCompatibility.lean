import Lax793645Proofs.Simplifications.OneCoverCompatibility
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SyntheticFailureBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Module Finset Filter
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N d : ℕ}

/-- Each of the two directed phase matrices factors through the span of
the offsets. If both diagonals vanish, four prescribed zeros follow
from a row support count. -/
theorem one_four_zero_span (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w) (V : Space (Ambient p (2*N)))
    (hV : ∀ x,w x≠0 → Δ x∈V)
    (hdiag : ∀ x,w x≠0 → ∀ i,joinPhase p (oneListens x) (unary i) (Δ x)=0) :
    1/(4*((dim V:ℝ)+1)^4)≤pr (pairW w w) (fun x=>oneQuench Δ x=repeatQ 0) := by
  classical
  let Z (x : OneUnit p n N) : V:=if hx : w x≠0 then ⟨Δ x,hV x hx⟩ else 0
  let U i (y : OneUnit p n N):=(joinPhase p (oneListens y) (unary i)).comp V.subtype
  let L i : Mat (OneUnit p n N) (OneUnit p n N):=Matrix.of (fun x y=>U i y (Z x))
  have hr i : (L i).rank≤dim V:=dual_matrix_rank Z (U i)
  have read (i) (x y) (hx : w x≠0) :
      L i x y=joinPhase p (oneListens y) (unary i) (Δ x) := by simp [L,U,Z,hx]
  have hd i x : L i x x=0 := by
    by_cases hx : w x≠0
    · exact (read i x x hx).trans (hdiag x hx i)
    have h : Z x=0:=dif_neg hx
    change U i x (Z x)=0
    rw [h,map_zero]
  refine (four_zero_probability (L false) (L true) w hw (dim V) (hr _) (hr _) (hd _) (hd _)).trans ?_
  apply pr_mono_support _ (pairW_law hw hw).nz
  rintro ⟨x,y⟩ hxy ⟨h₀,h₁,h₂,h₃⟩
  have hx:=left_ne_zero_of_mul hxy
  have hy:=right_ne_zero_of_mul hxy
  apply Prod.ext <;> funext i
  · cases i
    · exact (read false x y hx).symm.trans h₀
    · exact (read true x y hx).symm.trans h₁
  · cases i
    · exact (read false y x hy).symm.trans h₂
    · exact (read true y x hy).symm.trans h₃

/-- For either prescribed-one case, an obstruction on a large population is
necessary for compatibility to have less than inverse-rank probability.
The span only needs to contain offsets of units with positive weight. -/
theorem one_prescribed_one_span_alternative
    (Δ : OneUnit p n N → Ambient p (2*N)) (w : Wgt (OneUnit p n N)) (hw : IsLaw w)
    (V : Space (Ambient p (2*N))) (hV : ∀ x, w x ≠ 0 → Δ x ∈ V)
    (c : PredictionClass) (α : Party) (r : F)
    (hc : (∃ i, c = .dawn i ∧ α i = 0) ∨ c = .dusk ∧ r = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ε^2 / (4 * ((dim V : ℝ) + 1)^4) ≤ pr (pairW w w) (oneMatchUp Δ α r c) ∨
      ∃ I : OneUnit p n N → Prop, 1 - ε < pr w I ∧
        ∀ x, I x → w x ≠ 0 → ∀ y, I y → w y ≠ 0 → ¬ oneMatchUp Δ α r c (x,y) := by
  classical
  let Z (x : OneUnit p n N) : V := if hx : w x ≠ 0 then ⟨Δ x,hV x hx⟩ else 0
  let U i (x : OneUnit p n N) := (joinPhase p (oneListens x) (unary i)).comp V.subtype
  let L i : Mat (OneUnit p n N) (OneUnit p n N) := Matrix.of fun x y => U i y (Z x)
  have hr i : (L i).rank ≤ dim V := dual_matrix_rank Z (U i)
  have read i x y (hx : w x ≠ 0) : L i x y = joinPhase p (oneListens y) (unary i) (Δ x) := by
    simp [L,U,Z,hx]
  suffices ∃ B : Mat (OneUnit p n N) (OneUnit p n N), B.rank ≤ (dim V + 1)^4 ∧
      ∀ x y, w x ≠ 0 → w y ≠ 0 → (B x y ≠ 0 ↔ oneMatchUp Δ α r c (x,y)) by
    obtain ⟨B,hrank,hread⟩ := this
    rcases row_support_alternative B w hw _ (by positivity) hrank ε hε with h | ⟨I,hm,hi⟩
    · left
      simp only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] at h
      exact h.trans (pr_mono_support _ (pairW_law hw hw).nz fun ⟨x,y⟩ hxy =>
        (hread x y (left_ne_zero_of_mul hxy) (right_ne_zero_of_mul hxy)).mp)
    exact Or.inr ⟨I,hm,fun x hx hxp y hy hyp h =>
      ((hread x y hxp hyp).mpr h) (hi x hx y hy)⟩
  have bit (v : F) : v ≠ 0 ↔ v = 1 := by rcases bit_cases v with h|h <;> simp [h]
  rcases hc with ⟨i,rfl,hi⟩ | ⟨rfl,rfl⟩
  · refine ⟨L i + (L i)ᵀ, (mrk_add_le ..).trans ?_, ?_⟩
    · rw [Matrix.rank_transpose]
      have hpow := Nat.pow_le_pow_right (by omega : 0 < dim V + 1) (by decide : 2 ≤ 4)
      exact (Nat.add_le_add (hr i) (hr i)).trans (le_trans (by nlinarith only [Nat.zero_le ((dim V)^2)]) hpow)
    intro x y hx hy
    change L i x y + L i y x ≠ 0 ↔
      joinPhase p (oneListens y) (unary i) (Δ x) + joinPhase p (oneListens x) (unary i) (Δ y) =
        PredictionClass.firstBit α i
    rw [read i x y hx,read i y x hy,PredictionClass.firstBit,hi,add_zero,bit]
  · let Q := mpMask (L false) (L true)
    have hrQ : Q.rank ≤ (dim V)^2 := (rank_mask ..).trans (by
      rw [pow_two]; exact Nat.mul_le_mul (hr _) (hr _))
    refine ⟨mpMask Q Qᵀ, (rank_mask ..).trans ?_, ?_⟩
    · rw [Matrix.rank_transpose]
      calc Q.rank * Q.rank ≤ (dim V)^2 * (dim V)^2 := Nat.mul_le_mul hrQ hrQ
           _ = (dim V)^4 := by ring
           _ ≤ (dim V + 1)^4 := by gcongr; omega
    intro x y hx hy
    change (L false x y * L true x y) * (L false y x * L true y x) ≠ 0 ↔
      oneQuench Δ (x,y) = repeatQ 1
    rw [mul_ne_zero_iff,mul_ne_zero_iff,mul_ne_zero_iff]
    simp only [bit,read _ x y hx,read _ y x hy]
    constructor
    · rintro ⟨⟨a,b⟩,c,d⟩
      exact Prod.ext (funext fun i => Bool.rec a b i) (funext fun i => Bool.rec c d i)
    intro h
    exact ⟨⟨congrFun (congrArg Prod.fst h) false,congrFun (congrArg Prod.fst h) true⟩,
      congrFun (congrArg Prod.snd h) false,congrFun (congrArg Prod.snd h) true⟩

/-- The full four-bit pattern needs a bound on its singleton characters.
For its two even parities, an ambient matrix rank bound suffices for any law. -/
theorem one_four_pattern_ambient (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w)
    (hd : ∀ x,w x≠0→joinPhase p (oneListens x) allSide (Δ x)=0)
    (i : F) {E : ℝ} (he : 0≤E)
    (hχ : ∀ j : Bool,∀ S,|channelPitch Δ oneListens w (unary j) S|≤E) :
    1/(16*((dim (Ambient p (2*N)):ℝ)+1)^2)-E ≤
      pr (pairW w w) (fun x=>oneQuench Δ x=repeatQ i) := by
  classical
  let Z (x : OneUnit p n N) := if w x=0 then 0 else Δ x
  let D : Mat (OneUnit p n N) (OneUnit p n N) :=
    Matrix.of (fun x y=>joinPhase p (oneListens y) allSide (Z x))
  have hr : D.rank≤dim (Ambient p (2*N)) := dual_matrix_rank Z (fun x=>joinPhase p (oneListens x) allSide)
  have hdiag (x) : D x x=0 := by
    change joinPhase p (oneListens x) allSide (Z x)=0
    by_cases h : w x=0
    · simp [Z,h]
    simpa [Z,h] using hd x h
  have lower:=mutual_zero_probability D w hw _ hr hdiag
  have hy : pr (pairW w w) (fun x=>D x.1 x.2=0 ∧ D x.2 x.1=0)=
      pr (pairW w w) (fun x=>repeated (oneQuench Δ x)) := by
    refine avg_congr (fun x hx=>?_)
    apply congrArg ind
    unfold repeated oneQuench
    simp only [←one_tone_vec]
    simp [D,Z,left_ne_zero_of_mul hx,right_ne_zero_of_mul hx]
  rw [hy] at lower
  refine le_trans (sub_le_sub_right ?_ _) (one_tiny_pattern p Δ w i he hχ)
  calc
    _ = (1/4:ℝ) * (1/(4*((dim (Ambient p (2*N)):ℝ)+1)^2)) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left lower (by norm_num)

theorem eventually_ambient_pattern_margin (g : ℕ) :
    ∃ c>0,∀ᶠ N : ℕ in atTop,
      c/(N:ℝ)^4 ≤ 1/(16*((g:ℝ)*N*N+1)^2)-bp (-0.24*N) := by
  let c : ℝ := 1/(32*((g:ℝ)+1)^2)
  have hc : 0<c := by unfold c; positivity
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop 1,bp_poly_dom_nat (by norm_num : 0<(0.24:ℝ)) c⁻¹ 4] with N hN h
  have hN' : 1≤(N:ℝ) := by exact_mod_cast hN
  have hN2 : 1≤(N:ℝ)^2 := one_le_pow₀ hN'
  have den : (g:ℝ)*N*N+1≤(g+1)*N^2 := by nlinarith only [hN2]
  have main : 2*(c/(N:ℝ)^4)≤1/(16*((g:ℝ)*N*N+1)^2) := calc
    _ = 1/(16*(((g:ℝ)+1)*(N:ℝ)^2)^2) := by dsimp [c]; field_simp; ring
    _ ≤ _ := by gcongr
  have err : bp (-0.24*(N:ℝ))≤c/(N:ℝ)^4 := by
    rw [neg_mul,bp_neg]
    have hpos:=bp_pos (0.24*(N:ℝ))
    field_simp
    field_simp at h
    rw [mul_comm (N:ℝ) (0.24:ℝ)] at h
    simpa only [mul_comm c] using h.le
  linarith only [main,err]

set_option maxHeartbeats 600000 in
theorem one_tiny_pattern_mass (p : Shape) {n N : ℕ} (Δ : OneUnit p n N→Ambient p (2*N))
    (w : Wgt (OneUnit p n N)) (hw : IsLaw w)
    (h : oneTonalTiny Δ w d)
    (hd : ∀ x, w x≠0 → joinPhase p (oneListens x) allSide (Δ x) = 0) (i : F) :
    1/(16*((2*d:ℝ)*(2*N)+1)^2)-bp (-0.24*(2*N))≤
      pr (pairW w w) (fun x => oneQuench Δ x=repeatQ i) := by
  classical
  obtain ⟨T,hT,hZ,hE⟩ := h
  have hc : cdim p (oneSymCov T)≤2*d := by
    rw [cdim_sign]
    change oneCoverDimension T+oneCoverDimension T≤2*d
    omega
  let M := oneCircus (oneSymCov T) Δ w
  have hM : M.rank≤ (2*d)*(2*N) := (one_circus_rank (oneSymCov T) Δ w).trans ((Nat.mul_le_mul_left (2*N) hc).trans_eq
    (Nat.mul_comm _ _))
  have hB (x y) (hx : w x≠0) :
      joinPhase p (oneListens y) allSide (Δ x)=M x y := (one_shadow_valid (oneSymCov T) Δ hZ x y allSide hx).symm
  have hD x : M x x=0 := by
    by_cases hx : w x=0
    · change oneJuris (oneSymCov T) x _ (oneWeightedCover (oneSymCov T) Δ w x) = _
      simp [oneWeightedCover,hx]
    exact (hB _ _ hx).symm.trans (hd x hx)
  let u := pairW w w
  have hX :
      pr u (fun x => M x.1 x.2=0 ∧ M x.2 x.1=0)=
        pr u (fun x => repeated (oneQuench Δ x)) := by
    refine avg_congr (fun x hx => ?_)
    congr 1
    have h1 := hB x.1 x.2 (left_ne_zero_of_mul hx)
    have h2 := hB x.2 x.1 (right_ne_zero_of_mul hx)
    unfold repeated oneQuench
    simp only [←one_tone_vec,h1,h2]
  have lower := mutual_zero_probability M w hw ((2*d)*(2*N)) hM hD
  rw [show pairW w w=u from rfl,hX] at lower
  refine le_trans (sub_le_sub_right ?_ _) (one_tiny_pattern p Δ w i (bp_pos _).le hE)
  calc
    _ = (1/4 : ℝ) * (1 / (4 * ((((2*d)*(2*N):ℕ):ℝ) + 1)^2)) := by push_cast; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left lower (by norm_num)

/-- The prescribed four-bit pattern retains inverse-square probability after
the exponentially small character error. -/
theorem eventually_mutual_zero_margin (d : ℕ) :
    ∃ c > (0:ℝ), ∀ᶠ N : ℕ in atTop,
      c / N^2 ≤ 1 / (16 * ((d:ℝ)*N+1)^2) - bp (-0.24*N) := by
  let c : ℝ := 1 / (32 * ((d:ℝ)+1)^2)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop 1,
    bp_poly_dom_nat (by norm_num : 0 < (0.24:ℝ)) c⁻¹ 2] with N hN hexp
  have hN' : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hden : (d:ℝ)*N+1 ≤ (d+1)*N := by linarith only [hN']
  have hmain : 2 * (c / N^2) ≤ 1 / (16 * ((d:ℝ)*N+1)^2) := calc
    _ = 1 / (16 * (((d:ℝ)+1)*N)^2) := by dsimp [c]; rw [mul_pow]; field_simp; ring
    _ ≤ _ := by gcongr
  have herr : bp (-0.24*N) ≤ c / N^2 := by
    rw [neg_mul, bp_neg]
    have hpos := bp_pos (0.24*N)
    field_simp
    field_simp at hexp
    rw [mul_comm _ (0.24:ℝ)] at hexp
    linarith
  linarith

end
end Lax793645Proofs.Simplifications
