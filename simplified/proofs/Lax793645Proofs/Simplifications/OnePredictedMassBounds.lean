import Lax793645Proofs.Simplifications.OnePredictedFileCoverage

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneStation StatusAnalysis.DualAnalysis
open PreparationParameters PredictionClass Template Finset Matrix Function
open scoped BigOperators
noncomputable section
namespace OneOptions
variable {p : Shape} {n M s0 : ℕ} {b : PreparationParameters}

private theorem paired_mixture {A I : Type} [Fintype A] [Fintype I]
    (u : Wgt I) (V : I → Wgt A) (P : A×A → Prop) :
    pr (pairW (mixW u V) (mixW u V)) P =
      avg (pairW u u) (fun i => pr (pairW (V i.1) (V i.2)) P) := by
  rw [←mix_data]
  unfold pr
  rw [mixW_avg]

set_option maxHeartbeats 1500000 in
theorem predicted_mass_bounds (x : OneSketch p M) (s : OneLeafMixture p n (M*n))
    (v : OneStation p n (M*n) (onePreparationPins b) s) (m : cycleM p) (U : Wgt (OneUnit p n (M*n)))
    (hv : v.bank) (h : OneLead U s (m n) b.leafNew (2*b.ζ) (onePreparationPins b)) (hE : OneAnalyticParameters p M b s0)
    (hmarks : s.within (fun o => oneSeems b (m n) s o (fun i => x.g i n)
      (x.m n o) (x.L n o) x.α (x.ε n) ∧ glint p (x.m n o)=x.r ∧
      (x.c=dusk → oneExactInk (m n) (x.m n) o)))
    {η ε β : ℝ} {R : ℕ}
    (hclass : oneFiniteClass (fun i=>x.g i n) x.α=x.c)
    (hrows : OneAlgebraicRows (fun i=>x.g i n) R)
    (hcells : ∀ l q k, η≤oneWisp p (onePredictorPartition x.c (fun i=>x.g i n)) l q
      (onePredictorPartition x.c (fun i=>x.g i n) l q k))
    (hε : 0 ≤ ε) (hε' : x.ε n ≤ ε) (hβ : 0 < β)
    (hN : 2*num (Toast p)-((M*n:ℕ):ℝ) ≤ -1)
    (hcal : ∀ f : PredictedFile p (onePreparationPins b),
      ∀ Y : OneSilhouette p (M*n) predictorCellCount,
      (∀ i, η ≤ oneWisp p Y (f.1.2.2.t i) (f.1.2.2.z i) (f.2 i)) → f.large Y η) :
    let μ := s.sap U
    let C := oneMatchProg x n
    let S := oneSecureAt s
    let z := ∑ f : PredictedFile p (onePreparationPins b), f.mass v (m n) x.α (fun i => x.g i n) ε η x.c U β
    pr (pairW μ μ) (fun o => C o ∧ S o) ≤ 2*β*Fintype.card (PredictedFile p (onePreparationPins b))+z ∧
    (∀ γ : ℝ,oneCompatibilityFloor s U C γ → 2*β*Fintype.card (PredictedFile p (onePreparationPins b)) ≤ γ/2 →
      pr (pairW μ μ) C ≤ 2*pr (pairW μ μ) (fun o => C o ∧ ¬S o)+z) := by
  classical
  intro μ C S z
  let A k := partW U (Subtype.val (show s.T from k))
  let u := portionW U s.T
  let W := pairW u u
  have hA k : IsLaw (A k) := on_law h.law.nz (h.strength.leaf _ k.property).pos
  obtain ⟨hu,heq⟩ := rebuild h.law.nz h.strength.part (fun k hk => (h.strength.leaf _ hk).pos) h.amount
  have hW : IsLaw W := pairW_law hu hu
  let P f (i : s.T×s.T) := (f : PredictedFile p (onePreparationPins b)).leftTest v (m n) x.α (fun i => x.g i n) ε η x.c i.1 i.2
  let Q f (i : s.T×s.T) := (f : PredictedFile p (onePreparationPins b)).rightTest v (m n) x.α (fun i => x.g i n) ε η x.c i.1 i.2
  let G f := (f : PredictedFile p (onePreparationPins b)).event v (m n) x.α (fun i => x.g i n) ε η x.c U β
  have hhome i o (ho : A i o ≠ 0) : o ∈ i.val := (onW_ne ho).1
  have hcover (i : s.T×s.T) o (ho : pairW (A i.1) (A i.2) o ≠ 0) (hc : C o ∧ S o) :
      ∃ f, P f i o.1 ∧ Q f i o.2 :=
    predicted_file_coverage x s v m U hv h hE hmarks hclass hrows hcells hε hε' hN hcal
      i.1 i.2 o.1 o.2 (hhome _ _ (left_ne_zero_of_mul ho))
      (hhome _ _ (right_ne_zero_of_mul ho)) hc.1 hc.2
  have hsub i : substantialWitness (A i.1) (A i.2) (fun f => P f i) (fun f => Q f i) β →
      ∃ f, G f i := by
    rintro ⟨f,hf,hg⟩
    exact ⟨f,f.substantial_event v (m n) x.α (fun i => x.g i n) ε η x.c U hβ i.1 i.2 hA hf hg⟩
  have hmixture (P : OneUnit p n (M*n)×OneUnit p n (M*n) → Prop) :
      pr (pairW μ μ) P = avg W (fun i => pr (pairW (A i.1) (A i.2)) P) := by
    have he : μ=mixW u A := heq
    rw [he]
    exact paired_mixture u A P
  have hsum : pr W (fun i => ∃ f, G f i) ≤ z := pr_exists_le hW.nz G
  constructor
  · rw [hmixture]
    have hp (i : s.T×s.T) := finite_witness_bound (J:=PredictedFile p (onePreparationPins b))
      (A i.1) (A i.2) (hA i.1) (hA i.2)
      (fun o => C o ∧ S o) (fun f => P f i) (fun f => Q f i) (hcover i) β hβ.le
    have hb := avg_mono hW.nz fun i => (hp i).trans
      (add_le_add le_rfl (ind_mono (hsub i)))
    rw [avg_add,avg_const,hW.total,one_mul] at hb
    exact hb.trans (add_le_add le_rfl hsum)
  · intro γ hfloor hsize
    rw [hmixture,hmixture]
    have hp (i : s.T×s.T) := finite_witness_with_floor (J:=PredictedFile p (onePreparationPins b))
      (A i.1) (A i.2) (hA i.1) (hA i.2)
      C S (fun f => P f i) (fun f => Q f i) γ (hfloor i.1 i.2) (hcover i) β hβ.le hsize
    have hb := avg_mono hW.nz fun i => (hp i).trans
      (add_le_add le_rfl (ind_mono (hsub i)))
    rw [avg_add,avg_mul'] at hb
    exact hb.trans (add_le_add le_rfl hsum)

end OneOptions
end
end Lax793645Proofs.Simplifications
