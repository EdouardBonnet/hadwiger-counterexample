/-
Adapted from AnalyticParameters (OpenAI,
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0).
The asymptotic overlap upper bound uses the affine realization and input
rejection. The preparation law and independent leaf sampling are unchanged.
-/
import Lax793645Proofs.Simplifications.AffineParameters
import Lax793645Proofs.Simplifications.AffineQueryHistograms

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.Station PreparationParameters
open Filter Finset Matrix
open scoped BigOperators Topology
noncomputable section

structure AffineVeil (p : Shape) (M : ℕ) (b : PreparationParameters) (r : ℕ)
    (l : Filter ℕ) (m : cycleM p) (s : rhythms p M) (w : tale p M) : Prop where
  easel : AffineAnalyticParameters p M b r
  timeL : l ≤ atTop
  durableS : b.durable l p M m w s
  moment : ∀ᶠ n in l,b.nascent p (M*n) (w n) (m n) ∧ unaryGood (m n) b.pins r ∧
    binaryGood (m n) ∧ conflicted p (m n) (M*n) (w n)

variable {p : Shape} {n N K M r : ℕ} {q : Format} {d e : Rates}

private theorem affine_arena_pos {s : LeafMixture p n N} (v : Station p n N K s)
    (w : Typus p q d e) (m : Mixer p n) (μ : Wgt (UnitType p n N))
    (k : Fin (2^deckMax p K)) (h : 0 < s.amount μ) (hw : IsLaw μ) :
    0 ≤ AffineOptions.arena v w m μ k := by
  classical
  have hf (i : s.T) : 0 ≤ portionW μ s.T i := div_nonneg (pr_nonneg hw.nz) h.le
  have hg (S : CTile p n N) i : 0 ≤ partW μ S i := normW_nonneg (subW_nonneg hw.nz _) _
  refine avg_nonneg (fun _ => mul_nonneg (hf _) (hf _)) (fun i => avg_nonneg
    (unifOn_sub _).nz (fun x => mul_nonneg ?_ ?_))
  · exact div_nonneg (AffineOptions.sales_pos w.qA _ _ _ _ m _ _ _ (hg _) x)
      ((unifOn_sub _).nz _)
  exact div_nonneg (AffineOptions.sales_pos w.qB _ _ _ _ m _ _ _ (hg _) x)
    ((unifOn_sub _).nz _)

variable {b : PreparationParameters} {l : Filter ℕ} {m : cycleM p}
    {s : rhythms p M} {w : tale p M}

set_option maxHeartbeats 1200000 in
theorem AffineVeil.score_cost (h : AffineVeil p M b r l m s w)
    (v : Stations p M b.pins s) :
    ∃ δ : ℕ → ℝ,ExpSmall l (fun n=> ((M*n:ℕ):ℝ)) δ ∧
      ∀ᶠ n in l, ∀ (q : Format) (d e : Rates) (x : Typus p q d e) (k : Fin (2^deckMax p b.pins)),
        |AffineOptions.arena (v n) x (m n) (w n) k|≤δ n := by
  let N:=fun n : ℕ=> M*n; let z:=fun n=>((N n):ℝ)
  have hq := h.easel
  have ht := hq.enter.first
  have hz : Tendsto z l atTop := (trend_sizes l h.timeL ht.hM).2
  let C n:= ((s n).amount (w n))⁻¹
  have hc := h.durableS.mass.inv_cap
  let δ n := bp (-1*z n)*C n*C n + bp (-0.005*z n)*2
  have hd : ExpSmall l z δ :=
    (((ExpSmall.bp_n zero_lt_one).mul hc).mul hc).add hz
      ((ExpSmall.bp_n (by norm_num)).mul (expO_const hz _))
  refine ⟨δ,hd,?_⟩
  filter_upwards [h.moment,h.durableS.mass.positive,h.durableS.shape,hq.secure.filter_mono h.timeL]
    with n hn hN hA hB q d e x k
  have hm := hn.1.law
  rw [abs_of_nonneg (affine_arena_pos _ _ _ _ _ hN hm)]
  let u:=(s n).sap (w n)
  refine (AffineOptions.arena_bound (v n) x _ _ k hA.1 hm hN hB).trans ?_
  have hμ i : 0≤u i := (LeafMixture.sapLaw hN hm).nz _
  have hk i : u i ≤ C n*w n i := LeafMixture.upper_sap hm hN i
  have hv (x:UnitType p n (N n) × UnitType p n (N n)) :
      pairW u u x ≤ (C n*C n)*pairW (w n) (w n) x :=
    (mul_le_mul (hk _) (hk _) (hμ _) ((hμ _).trans (hk _))).trans_eq (by unfold pairW; ring)
  have hf : pr (pairW u u) (clash p (m n) (N n)) ≤
      (C n*C n)*bp (-200 * (z n)) := (pr_cap hv _).trans
        (mul_le_mul_of_nonneg_left hn.2.2.2.le (mul_self_nonneg _))
  unfold δ
  rw [mul_comm _ 2]
  refine add_le_add_left ((mul_le_mul_of_nonneg_left hf (bp_pos _).le).trans ?_) _
  calc _ = (beamPrice p (N n) * bp (-200 * z n))*(C n*C n) := by unfold beamPrice N; ring
       _ ≤ _ := (mul_le_mul_of_nonneg_right (beam_cost p (N n) ht.hG) (mul_self_nonneg _)).trans_eq
            (by unfold z; rw [neg_one_mul,mul_assoc])

set_option maxHeartbeats 1200000 in
theorem AffineVeil.upright (h : AffineVeil p M b r l m s w) :
    ∀ᶠ n in l,Align b r p M n (m n) ((s n).sap (w n)) := by
  let z n:= ((M*n:ℕ):ℝ)
  have ht := h.easel.enter.first
  have hM : 1 ≤ (M:ℝ) := by exact_mod_cast ht.hM
  let e : ℝ := 1/(128*M)
  have he : 0< e:=by unfold e; positivity
  have hz := (trend_sizes l h.timeL ht.hM).2
  let D n:=((s n).amount (w n))⁻¹
  filter_upwards [h.moment,h.durableS.mass.inv_cap e he,
    h.durableS.mass.positive,expO_const hz b.L e he, ht.wrap.filter_mono h.timeL,
    (eventually_ge_atTop (2*p.r)).filter_mono h.timeL] with n hn he' ht' hL hG hH
  have hw := hn.1.law
  have h1 (i) := LeafMixture.upper_sap hw ht' i
  have h2 : 0≤D n := (inv_pos_of_pos ht').le
  have hB : D n * b.L ≤ bp (1/32*(n:ℝ)) := by
    have hi : e*z n=(1/128)*(n:ℝ) := by unfold e z; push_cast; field_simp
    calc _ ≤ bp (e*z n)*bp (e*z n) :=
           mul_le_mul ((le_abs_self _).trans he') ((le_abs_self _).trans hL) ht.early.hL
             (bp_pos _).le
         _ ≤ _ := by rw [←bp_add,hi]; apply bp_le; linarith [(Nat.cast_nonneg n :0≤(n:ℝ))]
  have hv := LeafMixture.upperSide hn.1.border h1 h2 hB
  refine ⟨hn.2.2.1,hn.2.1,hH,hG.1, LeafMixture.sapLaw ht' hw, hv true,hv false,fun i=>?_⟩
  have hh := hn.1.total i
  apply ((h1 i).trans (mul_le_mul_of_nonneg_left hh h2)).trans
  rw [←mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (raw_nonneg ..) (raw_nonneg ..))
  have hx : e ≤1 := by unfold e; exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  refine (mul_le_mul_of_nonneg_right ((le_abs_self _).trans he') (bp_pos _).le).trans ?_
  rw [←bp_add]
  unfold spJoint; refine bp_le ?_; rw [←add_mul]
  exact mul_le_mul_of_nonneg_right (by linarith only [hx]) (by positivity)
end
end Lax793645Proofs.Simplifications
