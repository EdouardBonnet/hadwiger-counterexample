import Lax793645Proofs.Simplifications.PredictedFileCoverage

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.Station StatusAnalysis.DualAnalysis
open PreparationParameters PredictionClass Template Finset Matrix Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {n M s0 : ℕ} {b : PreparationParameters}

private theorem paired_mixture {A I : Type} [Fintype A] [Fintype I]
    (u : Wgt I) (V : I → Wgt A) (P : A×A → Prop) :
    pr (pairW (mixW u V) (mixW u V)) P =
      avg (pairW u u) (fun i => pr (pairW (V i.1) (V i.2)) P) := by
  rw [←mix_data]
  unfold pr
  rw [mixW_avg]

set_option maxHeartbeats 1500000 in
theorem predicted_mass_bounds (x : Sketch p M) (s : LeafMixture p n (M*n))
    (v : Station p n (M*n) b.pins s) (m : cycleM p) (U : Wgt (UnitType p n (M*n)))
    (hv : v.bank) (h : Lead U s (m n) b) (hE : AnalyticParameters p M b s0)
    (hmarks : s.within (fun o => b.seems p (m n) s o (fun i => x.g i n)
      (x.m n o) (x.L n o) x.α (x.ε n) ∧ glint p (x.m n o)=x.r ∧
      (x.c=dusk → exactInk p (m n) (x.m n) o)))
    {τ η ε β : ℝ} (hrec : x.c.recital p (fun i => x.g i n) x.α τ)
    (hη : 0 ≤ η) (hτ : (predictorCellCount:ℝ)*η ≤ τ) (hsmall : 2*τ < 1)
    (hε : 0 ≤ ε) (hε' : x.ε n ≤ ε) (hβ : 0 < β)
    (hN : 2*num (Toast p)-((M*n:ℕ):ℝ) ≤ -1)
    (hcal : ∀ f : PredictedFile p b.pins,
      ∀ Y : Silhouette p (M*n) predictorCellCount,
      (∀ i, η ≤ wisp p Y (f.1.2.2.t i) (f.1.2.2.z i) (f.2 i)) → f.large Y η) :
    let μ := s.sap U
    let C := matchProg x n
    let S := secureAt p s.rooting
    let z := ∑ f : PredictedFile p b.pins, f.mass v (m n) x.α (fun i => x.g i n) ε η x.c U β
    pr (pairW μ μ) (fun o => C o ∧ S o) ≤ 2*β*Fintype.card (PredictedFile p b.pins)+z ∧
    (b.hardened p (M*n) s (x.m n) → 2*β*Fintype.card (PredictedFile p b.pins) ≤ 1/2 →
      pr (pairW μ μ) C ≤ 2*pr (pairW μ μ) (fun o => C o ∧ ¬S o)+z) := by
  classical
  intro μ C S z
  let A k := partW U (Subtype.val (show s.T from k))
  let u := portionW U s.T
  let W := pairW u u
  have hA k : IsLaw (A k) := on_law h.law.nz (h.strength.leaf _ k.property).pos
  obtain ⟨hu,heq⟩ := rebuild h.law.nz h.strength.part (fun k hk => (h.strength.leaf _ hk).pos) h.amount
  have hW : IsLaw W := pairW_law hu hu
  let P f (i : s.T×s.T) := (f : PredictedFile p b.pins).leftTest v (m n) x.α (fun i => x.g i n) ε η x.c i.1 i.2
  let Q f (i : s.T×s.T) := (f : PredictedFile p b.pins).rightTest v (m n) x.α (fun i => x.g i n) ε η x.c i.1 i.2
  let G f := (f : PredictedFile p b.pins).event v (m n) x.α (fun i => x.g i n) ε η x.c U β
  have hhome i o (ho : A i o ≠ 0) : o ∈ i.val := (onW_ne ho).1
  have hcover (i : s.T×s.T) o (ho : pairW (A i.1) (A i.2) o ≠ 0) (hc : C o ∧ S o) :
      ∃ f, P f i o.1 ∧ Q f i o.2 :=
    predicted_file_coverage x s v m U hv h hE hmarks hrec hη hτ hsmall hε hε' hN hcal
      i.1 i.2 o.1 o.2 (hhome _ _ (left_ne_zero_of_mul ho))
      (hhome _ _ (right_ne_zero_of_mul ho)) hc.1 hc.2
  have hsub i : substantialWitness (A i.1) (A i.2) (fun f => P f i) (fun f => Q f i) β →
      ∃ f, G f i := by
    rintro ⟨f,hf,hg⟩
    exact ⟨f,f.substantial_event v (m n) x.α (fun i => x.g i n) ε η x.c U hβ i.1 i.2 hA hf hg⟩
  have hmixture (P : UnitType p n (M*n)×UnitType p n (M*n) → Prop) :
      pr (pairW μ μ) P = avg W (fun i => pr (pairW (A i.1) (A i.2)) P) := by
    have he : μ=mixW u A := heq
    rw [he]
    exact paired_mixture u A P
  have hsum : pr W (fun i => ∃ f, G f i) ≤ z := pr_exists_le hW.nz G
  constructor
  · rw [hmixture]
    have hp (i : s.T×s.T) := finite_witness_bound (J:=PredictedFile p b.pins)
      (A i.1) (A i.2) (hA i.1) (hA i.2)
      (fun o => C o ∧ S o) (fun f => P f i) (fun f => Q f i) (hcover i) β hβ.le
    have hb := avg_mono hW.nz fun i => (hp i).trans
      (add_le_add le_rfl (ind_mono (hsub i)))
    rw [avg_add,avg_const,hW.total,one_mul] at hb
    exact hb.trans (add_le_add le_rfl hsum)
  · intro hhard hsize
    have hconst (i : s.T×s.T) : 0 < pr (pairW (A i.1) (A i.2)) C →
        pr (pairW (A i.1) (A i.2)) C=1 := by
      intro hpos
      obtain ⟨o,hco,ho⟩ := exists_of_pr_pos (pairW_law (hA i.1) (hA i.2)).nz hpos
      obtain ⟨T,hT,hcov,hpin⟩ := hhard
      obtain ⟨a,ha,_⟩ := hpin _ i.1.property
      obtain ⟨b0,hb,_⟩ := hpin _ i.2.property
      have hall y (hy : pairW (A i.1) (A i.2) y ≠ 0) : C y := by
        have hy1 := hhome _ _ (left_ne_zero_of_mul hy)
        have hy2 := hhome _ _ (right_ne_zero_of_mul hy)
        have he := phase_fixed (x.m n) T _ _ _ _ ha hb hy1
          (hhome _ _ (left_ne_zero_of_mul ho.ne')) hy2 (hhome _ _ (right_ne_zero_of_mul ho.ne'))
          (hcov _ i.1.property _ hy1) (hcov _ i.2.property _ hy2)
        change x.c.compatible x.α x.r (quench p (delta (x.m n)) y)
        rw [he]
        exact hco
      calc
        _ = pr (pairW (A i.1) (A i.2)) (fun _ => True) := by
          apply avg_congr
          intro y hy
          change ind (C y)=ind True
          rw [ind_one (hall y hy),ind_true]
        _ = 1 := by rw [pr_true,(pairW_law (hA i.1) (hA i.2)).total]
    rw [hmixture,hmixture]
    have hp (i : s.T×s.T) := finite_witness_rare (J:=PredictedFile p b.pins)
      (A i.1) (A i.2) (hA i.1) (hA i.2)
      C S (fun f => P f i) (fun f => Q f i) (hconst i) (hcover i) β hβ.le hsize
    have hb := avg_mono hW.nz fun i => (hp i).trans
      (add_le_add le_rfl (ind_mono (hsub i)))
    rw [avg_add,avg_mul'] at hb
    exact hb.trans (add_le_add le_rfl hsum)

end
end Lax793645Proofs.Simplifications
