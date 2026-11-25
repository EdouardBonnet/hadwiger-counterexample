import Lax793645Proofs.Simplifications.OnePredictedOptions
import Lax793645Proofs.Simplifications.OnePredictedPairedBounds
import Lax793645Proofs.Simplifications.FiniteWitnessTransfer


namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneStation StatusAnalysis.DualAnalysis PreparationParameters PredictionClass Template
open Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section
namespace OneOptions

abbrev PredictedFile (p : Shape) (K : ℕ) :=
  Σ i : OneScrip p K, Messenger (toFormat i.1.1) → Fin predictorCellCount

namespace PredictedFile
variable {p : Shape} {K n N : ℕ} (f : PredictedFile p K)

def cell (Y : OneSilhouette p N predictorCellCount) :=
  oneTupleCell Y f.1.2.2.t f.1.2.2.z f.2
def floor (η : ℝ) : ℝ := η^Fintype.card (Messenger (toFormat f.1.1.1))/2
def large (Y : OneSilhouette p N predictorCellCount) (η : ℝ) :=
  f.floor η ≤ pr (oneLawNu p N f.1.2.2.t f.1.2.2.z) (f.cell Y)

variable {s : OneLeafMixture p n N} (v : OneStation p n N K s) (m : Mixer p n)
    (α : Party) (g : Bool → OneAugur p N) (ε η : ℝ) (c : PredictionClass)

def leftTest (i j : s.T) (o : OneUnit p n N) :=
  f.large (onePredictorPartition c g) η ∧
  frontPage v f.1.2.2 m i j f.1.2.1 o ∧
  OneQuill.OneBaseSteady f.1.2.2.qA m K (v.cAxes i (toRates f.1.1.2.1)) o ∧
  OneQuill.OnePredictionReady f.1.2.2.qA f.1.2.2.t f.1.2.2.z (v.cAxes i (toRates f.1.1.2.1))
    m α (onePreparedPredictor c g) ε (f.cell (onePredictorPartition c g)) o

def rightTest (i j : s.T) (o : OneUnit p n N) :=
  f.large (onePredictorPartition c g) η ∧
  backPage v f.1.2.2 m i j f.1.2.1 o ∧
  OneQuill.OneBaseSteady f.1.2.2.qB m K (v.cAxes j (toRates f.1.1.2.2)) o ∧
  OneQuill.OnePredictionReady f.1.2.2.qB f.1.2.2.t f.1.2.2.z (v.cAxes j (toRates f.1.1.2.2))
    m α (onePreparedPredictor c g) ε (f.cell (onePredictorPartition c g)) o

def event (U : Wgt (OneUnit p n N)) (β : ℝ) (i : s.T×s.T) :=
  f.large (onePredictorPartition c g) η ∧
  predictedCharter v f.1.2.2 m f.1.2.1 U β α (onePreparedPredictor c g) ε
    (f.cell (onePredictorPartition c g)) i

def mass (U : Wgt (OneUnit p n N)) (β : ℝ) :=
  pr (pairW (portionW U s.T) (portionW U s.T)) (f.event v m α g ε η c U β)

theorem substantial_event (U : Wgt (OneUnit p n N)) {β : ℝ} (hβ : 0 < β)
    (i j : s.T) (hU : ∀ k : s.T, IsLaw (partW U k.val))
    (hleft : 2*β ≤ pr (partW U i.val) (f.leftTest v m α g ε η c i j))
    (hright : 2*β ≤ pr (partW U j.val) (f.rightTest v m α g ε η c i j)) :
    f.event v m α g ε η c U β (i,j) := by
  obtain ⟨o,ho,_⟩ := exists_of_pr_pos (hU i).nz ((by positivity : 0 < 2*β).trans_le hleft)
  refine ⟨ho.1,ho.2.1.1.1, f.leftTest v m α g ε η c i j,
    f.rightTest v m α g ε η c i j,fun o h => h.2.1,fun o h => h.2.1,
    ⟨hleft,fun o h _ => h.2.2⟩,⟨hright,fun o h _ => h.2.2⟩⟩

end PredictedFile

theorem predicted_file_calendar {p : Shape} {M K : ℕ} {l : Filter ℕ}
    (hl : l ≤ atTop) (hM : 1 ≤ M) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in l, ∀ f : PredictedFile p K,
      ∀ Y : OneSilhouette p (M*n) predictorCellCount,
      (∀ i, η ≤ oneWisp p Y (f.1.2.2.t i) (f.1.2.2.z i) (f.2 i)) → f.large Y η := by
  classical
  rw [eventually_all]
  intro f
  have hz := (trend_sizes l hl hM).2
  have hN := hz.eventually (eventually_ge_atTop (2*num (Messenger (toFormat f.1.1.1)×Toast p)+2))
  have hlim := (((bp_tendsto_zero (by norm_num : (0:ℝ)<1/2)).comp hz).const_mul
    (2*quadraticNetFact (trayPort p f.1.2.2.t)))
  have herr := hlim.eventually (eventually_le_nhds
    (by simpa only [mul_zero] using (half_pos (pow_pos hη (Fintype.card (Messenger (toFormat f.1.1.1)))))))
  filter_upwards [hN,herr] with n hn he Y hy
  apply one_tuple_cell_mass Y _ _ _ hη.le hy (by linarith only [hn])
  simpa only [Function.comp_apply,show -(1/2:ℝ)*((M*n:ℕ):ℝ) = -((M*n:ℕ):ℝ)/2 from by ring] using he

theorem predicted_file_small {p : Shape} {M r : ℕ} {b : PreparationParameters} {l : Filter ℕ}
    {m : cycleM p} {s : OneRhythms p M} {w : OneTale p M}
    (v : OneStations p M (onePreparationPins b) s) (h : OneVeil p M b r l m s w)
    (f : PredictedFile p (onePreparationPins b)) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) (hη1 : η ≤ 1)
    (c : PredictionClass) (α : Party) (g : ∀ n, Bool → OneAugur p (M*n))
    (ε : ℕ → ℝ) (heps : Tendsto ε l (𝓝 0)) :
    ExpSmall l (fun n => (n:ℝ)) (fun n => f.mass (v n) (m n) α (g n) (ε n) η c (w n) β) := by
  classical
  let E n := f.cell (onePredictorPartition c (g n))
  let E' n := if f.large (onePredictorPartition c (g n)) η then E n else fun _ => True
  have h0 : 0 < f.floor η := half_pos (pow_pos hη _)
  have h1 : f.floor η ≤ 1 := by
    have hp := pow_le_one₀ (n:=Fintype.card (Messenger (toFormat f.1.1.1))) hη.le hη1
    unfold PredictedFile.floor
    linarith only [hp]
  have hE : ∀ᶠ n in l, f.floor η ≤ pr (oneLawNu p (M*n) f.1.2.2.t f.1.2.2.z) (E' n) := by
    filter_upwards [(trend_sizes l h.time h.parameters.unary.hM).2.eventually
      (eventually_ge_atTop (2*num (Messenger (toFormat f.1.1.1)×Toast p)+2))] with n hn
    by_cases hlarge : f.large (onePredictorPartition c (g n)) η
    · simpa only [E',if_pos hlarge] using (show f.floor η ≤ pr _ (E n) from hlarge)
    · simp only [E',if_neg hlarge,pr_true]
      rw [(one_nu_law f.1.2.2.t f.1.2.2.z (by linarith only [hn])).total]
      exact h1
  have hEdesign n : OneDesign f.1.2.2.t (fun k=>ind (E' n k)) 1 := by
    dsimp only [E']
    split_ifs with hlarge
    · exact one_tuple_cell_design (onePredictorPartition c (g n)) f.1.2.2.t f.1.2.2.z f.2
    · simpa only [implies_true,ind_true] using
        one_unary_product_design (N:=M*n) f.1.2.2.t (fun _ _=>True)
  apply (one_predicted_dim_berth v h f.1.2.2 f.1.2.1 hβ α
    (fun n => onePreparedPredictor c (g n)) ε heps E' h0 hE hEdesign).mono
  filter_upwards [h.moment,h.durable.shape,h.durable.mass.positive] with n hn hs hm
  have hu := (rebuild hn.1.law.nz hs.1.part (fun i hi => (hs.1.leaf i hi).pos) hm).1
  unfold PredictedFile.mass predictedBerth
  rw [abs_of_nonneg (pr_nonneg (pairW_law hu hu).nz),abs_of_nonneg (pr_nonneg (pairW_law hu hu).nz)]
  apply pr_mono (pairW_law hu hu).nz
  intro i hi
  simpa only [E',if_pos hi.1] using hi.2

end OneOptions
end
end Lax793645Proofs.Simplifications
