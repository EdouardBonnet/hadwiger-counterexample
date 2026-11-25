import Lax793645Proofs.Simplifications.RetainedPredictors
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PredictionClassBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis PredictionClass Template
open Finset Matrix Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {N r : ℕ}

def predictorCellCount : ℕ := Fintype.card (F×F)
theorem predictorCellCount_eq : predictorCellCount=4 := by decide

def preparedPredictor (c : PredictionClass) (g : Bool → Augur p N) : Bool → Augur p N :=
  if c=dusk then 0 else g

def predictorPartition (c : PredictionClass) (g : Bool → Augur p N) :
    Silhouette p N predictorCellCount :=
  fun l q k => Fintype.equivFin (F×F)
    (preparedPredictor c g true l q k,preparedPredictor c g false l q k)

def predictorPulse (c : PredictionClass) : Bool → Pulsar p predictorCellCount :=
  fun i _ _ k => if c=dusk then 0 else if i then
    ((Fintype.equivFin (F×F)).symm k).1 else ((Fintype.equivFin (F×F)).symm k).2

theorem predictor_pulse_eq (c : PredictionClass) (g : Bool → Augur p N) (i : Bool) :
    fromPulse (predictorPartition c g) (predictorPulse c i)=preparedPredictor c g i := by
  classical
  funext l q k
  by_cases hc : c=dusk
  · simp [fromPulse,predictorPulse,preparedPredictor,hc]
  · cases i <;> simp [fromPulse,predictorPulse,predictorPartition,preparedPredictor,hc]

theorem predictor_chorus {A B : Rates} (c : PredictionClass) (g : Bool → Augur p N)
    (α : Party) (τ : ℝ) (hrec : c.recital p g α τ)
    (X : ∀ i, Cell (A i)) (Y : ∀ i, Cell (B i)) :
    chorusClass p (⟨α,predictorPulse c,X,Y⟩ : PredictionData p A B predictorCellCount)
      (wisp p (predictorPartition c g)) c τ := by
  apply paintChorus c (predictorPartition c g) (predictorPulse c) g α τ _ X Y
  refine ⟨hrec.1,fun hc i => ?_,fun hc i => ?_,hrec⟩
  · rw [predictor_pulse_eq]
    simp only [preparedPredictor,if_neg hc]
  · funext l q k
    simp [predictorPulse,hc]

def tupleCell {q : Format} (Y : Silhouette p N r)
    (t : Tagging p (Messenger q)) (z : Messenger q → F) (k : Messenger q → Fin r) :
    Keys (p:=p) t N → Prop := fun x => ∀ i, Y (t i) (z i) (x i)=k i

theorem tuple_cell_mass {q : Format} (Y : Silhouette p N r)
    (t : Tagging p (Messenger q)) (z : Messenger q → F) (k : Messenger q → Fin r)
    {η : ℝ} (hη : 0 ≤ η) (hk : ∀ i, η ≤ wisp p Y (t i) (z i) (k i))
    (hN : 2*num (Messenger q×Toast p)-(N:ℝ) ≤ -1)
    (herr : 2*netFact (trayPort p t)*bp (-(N:ℝ)/2) ≤
      η^Fintype.card (Messenger q)/2) :
    η^Fintype.card (Messenger q)/2 ≤ pr (lawNu p N t z) (tupleCell Y t z k) := by
  classical
  let f i : Wgt (AtomKey (p:=p) (t i) N) := fun x => ind (Y (t i) (z i) x=k i)
  have hbound i x : |f i x| ≤ 1 :=
    (abs_of_nonneg (ind_nonneg _)).trans_le (ind_le_one _)
  have he := reference_product t z f hbound hN
  have hp : η^Fintype.card (Messenger q) ≤ ∏ i,avg (lawOmega p N (t i) (z i)) (f i) := by
    rw [show η^Fintype.card (Messenger q)=∏ _i : Messenger q,η from by simp]
    exact Finset.prod_le_prod (fun _ _ => hη) (fun i _ => hk i)
  have hprod : prodW f = fun x => ind (tupleCell Y t z k x) := by
    funext x
    exact (ind_all (fun i => Y (t i) (z i) (x i)=k i)).symm
  rw [hprod] at he
  have hleft := (abs_le.mp he).1
  change -_ ≤ pr (lawNu p N t z) (tupleCell Y t z k)-_ at hleft
  linarith only [hp,hleft,herr]

end
end Lax793645Proofs.Simplifications
