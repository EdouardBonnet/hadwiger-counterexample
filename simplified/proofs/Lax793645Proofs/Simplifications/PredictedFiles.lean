import Lax793645Proofs.Simplifications.PredictedOptionRealization
import Lax793645Proofs.Simplifications.PredictedPairedBounds
import Lax793645Proofs.Simplifications.FiniteWitnessTransfer

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.Station StatusAnalysis.DualAnalysis PreparationParameters PredictionClass Template
open Filter Finset Matrix Function
open scoped BigOperators Topology
noncomputable section

abbrev PredictedFile (p : Shape) (K : ℕ) :=
  Σ i : Scrip p K, Messenger (toFormat i.1.1) → Fin predictorCellCount

namespace PredictedFile
variable {p : Shape} {K n N : ℕ} (f : PredictedFile p K)

def cell (Y : Silhouette p N predictorCellCount) :=
  tupleCell Y f.1.2.2.t f.1.2.2.z f.2
def floor (η : ℝ) : ℝ := η^Fintype.card (Messenger (toFormat f.1.1.1))/2
def large (Y : Silhouette p N predictorCellCount) (η : ℝ) :=
  f.floor η ≤ pr (lawNu p N f.1.2.2.t f.1.2.2.z) (f.cell Y)

variable {s : LeafMixture p n N} (v : Station p n N K s) (m : Mixer p n)
    (α : Party) (g : Bool → Augur p N) (ε η : ℝ) (c : PredictionClass)

def leftTest (i j : s.T) (o : UnitType p n N) :=
  f.large (predictorPartition c g) η ∧
  v.frontPage f.1.2.2 m i j f.1.2.1 o ∧
  f.1.2.2.qA.baseSteady m K (v.cAxes i (toRates f.1.1.2.1)) o ∧
  f.1.2.2.qA.predictionReady f.1.2.2.t f.1.2.2.z (v.cAxes i (toRates f.1.1.2.1))
    m α (preparedPredictor c g) ε (f.cell (predictorPartition c g)) o

def rightTest (i j : s.T) (o : UnitType p n N) :=
  f.large (predictorPartition c g) η ∧
  v.backPage f.1.2.2 m i j f.1.2.1 o ∧
  f.1.2.2.qB.baseSteady m K (v.cAxes j (toRates f.1.1.2.2)) o ∧
  f.1.2.2.qB.predictionReady f.1.2.2.t f.1.2.2.z (v.cAxes j (toRates f.1.1.2.2))
    m α (preparedPredictor c g) ε (f.cell (predictorPartition c g)) o

def event (U : Wgt (UnitType p n N)) (β : ℝ) (i : s.T×s.T) :=
  f.large (predictorPartition c g) η ∧
  v.predictedCharter f.1.2.2 m f.1.2.1 U β α (preparedPredictor c g) ε
    (f.cell (predictorPartition c g)) i

def mass (U : Wgt (UnitType p n N)) (β : ℝ) :=
  pr (pairW (portionW U s.T) (portionW U s.T)) (f.event v m α g ε η c U β)

theorem substantial_event (U : Wgt (UnitType p n N)) {β : ℝ} (hβ : 0 < β)
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
      ∀ Y : Silhouette p (M*n) predictorCellCount,
      (∀ i, η ≤ wisp p Y (f.1.2.2.t i) (f.1.2.2.z i) (f.2 i)) → f.large Y η := by
  classical
  rw [eventually_all]
  intro f
  have hz := (trend_sizes l hl hM).2
  have hN := hz.eventually (eventually_ge_atTop (2*num (Messenger (toFormat f.1.1.1)×Toast p)+1))
  have hlim := (((bp_tendsto_zero (by norm_num : (0:ℝ)<1/2)).comp hz).const_mul
    (2*netFact (trayPort p f.1.2.2.t)))
  have herr := hlim.eventually (eventually_le_nhds
    (by simpa only [mul_zero] using (half_pos (pow_pos hη (Fintype.card (Messenger (toFormat f.1.1.1)))))))
  filter_upwards [hN,herr] with n hn he Y hy
  apply tuple_cell_mass Y _ _ _ hη.le hy (by linarith only [hn])
  simpa only [Function.comp_apply,show -(1/2:ℝ)*((M*n:ℕ):ℝ) = -((M*n:ℕ):ℝ)/2 from by ring] using he

theorem predicted_file_small {p : Shape} {M r : ℕ} {b : PreparationParameters} {l : Filter ℕ}
    {m : cycleM p} {s : rhythms p M} {w : tale p M}
    (v : Stations p M b.pins s) (h : veil p M b r l m s w)
    (f : PredictedFile p b.pins) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) (hη1 : η ≤ 1)
    (c : PredictionClass) (α : Party) (g : ∀ n, Bool → Augur p (M*n))
    (ε : ℕ → ℝ) (heps : Tendsto ε l (𝓝 0)) :
    ExpSmall l (fun n => (n:ℝ)) (fun n => f.mass (v n) (m n) α (g n) (ε n) η c (w n) β) := by
  classical
  let E n := f.cell (predictorPartition c (g n))
  let E' n := if f.large (predictorPartition c (g n)) η then E n else fun _ => True
  have h0 : 0 < f.floor η := half_pos (pow_pos hη _)
  have h1 : f.floor η ≤ 1 := by
    have hp := pow_le_one₀ (n:=Fintype.card (Messenger (toFormat f.1.1.1))) hη.le hη1
    unfold PredictedFile.floor
    linarith only [hp]
  have hE : ∀ᶠ n in l, f.floor η ≤ pr (lawNu p (M*n) f.1.2.2.t f.1.2.2.z) (E' n) := by
    filter_upwards [(trend_sizes l h.timeL h.easel.enter.first.hM).2.eventually
      (eventually_ge_atTop (2*num (Messenger (toFormat f.1.1.1)×Toast p)+1))] with n hn
    by_cases hlarge : f.large (predictorPartition c (g n)) η
    · simpa only [E',if_pos hlarge] using (show f.floor η ≤ pr _ (E n) from hlarge)
    · simp only [E',if_neg hlarge,pr_true]
      rw [(nuLaw f.1.2.2.t f.1.2.2.z (by linarith only [hn])).total]
      exact h1
  apply (predicted_dimBerth v h f.1.2.2 f.1.2.1 hβ α
    (fun n => preparedPredictor c (g n)) ε heps E' h0 hE).mono
  filter_upwards [h.moment,h.durableS.shape,h.durableS.mass.positive] with n hn hs hm
  have hu := (rebuild hn.1.law.nz hs.1.part (fun i hi => (hs.1.leaf i hi).pos) hm).1
  unfold PredictedFile.mass predictedBerth
  rw [abs_of_nonneg (pr_nonneg (pairW_law hu hu).nz),abs_of_nonneg (pr_nonneg (pairW_law hu hu).nz)]
  apply pr_mono (pairW_law hu hu).nz
  intro i hi
  simpa only [E',if_pos hi.1] using hi.2

end
end Lax793645Proofs.Simplifications
