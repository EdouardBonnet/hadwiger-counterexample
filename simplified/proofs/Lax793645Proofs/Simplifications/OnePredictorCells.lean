import Lax793645Proofs.Simplifications.PredictorCells
import Lax793645Proofs.Simplifications.OneFiniteReferenceGap
import Lax793645Proofs.Simplifications.OneFinitePredictions
import Lax793645Proofs.Simplifications.OnePredictionClasses
import Lax793645Proofs.Simplifications.OneReferenceProducts
import Lax793645Proofs.Simplifications.OneProductTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis PredictionClass Template Filter
open Finset Matrix Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {N r:ℕ}

def onePreparedPredictor (c:PredictionClass) (g:Bool→OneAugur p N):Bool→OneAugur p N:=
  if c=dusk then 0 else g

def onePredictorPartition (c:PredictionClass) (g:Bool→OneAugur p N):
    OneSilhouette p N predictorCellCount:=
  fun l q k=>Fintype.equivFin (F×F)
    (onePreparedPredictor c g true l q k,onePreparedPredictor c g false l q k)

theorem one_predictor_pulse_eq (c:PredictionClass) (g:Bool→OneAugur p N) (i:Bool):
    oneFromPulse (onePredictorPartition c g) (predictorPulse c i)=onePreparedPredictor c g i := by
  funext l q k
  by_cases hc:c=dusk
  · simp [oneFromPulse,predictorPulse,onePreparedPredictor,hc]
  · cases i <;> simp [oneFromPulse,predictorPulse,onePredictorPartition,onePreparedPredictor,hc]

def oneSilhouetteCoordinates (Y:OneSilhouette p N r):Silhouette p N r:=
  fun l q k=>Y l q ((oneAtomSplit l N).symm k)

theorem one_wisp_coordinates (Y:OneSilhouette p N r):
    oneWisp p Y=wisp p (oneSilhouetteCoordinates Y) := by
  funext l q
  unfold oneWisp oneSilhouetteCoordinates wisp oneLawOmega
  funext k
  change pr (mapW _ _) _=pr _ _
  rw [mapW_pr]

theorem one_predictor_chorus {A B:Rates} (c:PredictionClass) (g:Bool→OneAugur p N)
    (α:Party) (τ:ℝ) (hrec:oneRecital c g α τ)
    (X:∀ i,Cell (A i)) (Y:∀ i,Cell (B i)):
    chorusClass p (⟨α,predictorPulse c,X,Y⟩:PredictionData p A B predictorCellCount)
      (oneWisp p (onePredictorPartition c g)) c τ := by
  rw [one_wisp_coordinates]
  apply paintChorus c (oneSilhouetteCoordinates (onePredictorPartition c g))
    (predictorPulse c) (fun i=>oneAugurCoordinates (g i)) α τ _ X Y
  refine ⟨hrec.1,fun hc i=>?_,fun hc i=>?_,hrec⟩
  · funext l q k
    have he:=congrFun (congrFun (congrFun (one_predictor_pulse_eq c g i) l) q)
      ((oneAtomSplit l N).symm k)
    simpa only [onePreparedPredictor,if_neg hc,oneFromPulse,fromPulse,oneSilhouetteCoordinates,oneAugurCoordinates] using he
  · funext l q k
    simp [predictorPulse,hc]

/-- Each predictor cell that occurs at an ambient key has a fixed lower
mass on the prescribed Gram slice. The bound is independent of the maps. -/
theorem one_predictor_cell_calendar (p : Shape) (M R : ℕ) (hM : 1≤M) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ c (g : Bool→OneAugur p (M*n)),
      OneAlgebraicRows g R → ∀ l q x,
      bp (-((2*R:ℕ):ℝ))/2 ≤ oneWisp p (onePredictorPartition c g) l q
        (onePredictorPartition c g l q x) := by
  classical
  filter_upwards [one_attained_cell_calendar p M (2*R) hM] with n h c g hg l q x
  apply h
  have hr (i : Bool) : OneLinearAugur (onePreparedPredictor c g i) R := by
    by_cases hd : c=dusk
    · intro l
      rw [onePreparedPredictor,if_pos hd]
      change HasLinearCells (fun (_ : F) (_ : OneAtomKey (p:=p) l (M*n)) => (0:F)) R
      exact linear_cells_mono (linear_cells_constant (fun _ : F => (0:F))) (Nat.zero_le R)
    · simpa only [onePreparedPredictor,if_neg hd] using hg.rows i
  have hs:=linear_cells_bundle (fun _ : Bool=>R)
    (fun i=>onePreparedPredictor c g i l) (fun i=>hr i l)
  have ht:=linear_cells_postprocess hs (fun (_ : F) (v : Bool→F)=>
    Fintype.equivFin (F×F) (v true,v false))
  change HasLinearCells (fun q x => Fintype.equivFin (F×F)
    (onePreparedPredictor c g true l q x,onePreparedPredictor c g false l q x)) _
  simpa only [Finset.sum_const,Finset.card_univ,
    Fintype.card_bool,nsmul_eq_mul,Nat.cast_ofNat] using ht

def oneTupleCell {q:Format} (Y:OneSilhouette p N r)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (k:Messenger q→Fin r):
    OneKeys t N→Prop:=fun x=>∀ i,Y (t i) (z i) (x i)=k i

theorem one_tuple_cell_design {q:Format} (Y:OneSilhouette p N r)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (k:Messenger q→Fin r):
    OneDesign t (fun x=>ind (oneTupleCell Y t z k x)) 1:=
  one_unary_product_design t (fun i x=>Y (t i) (z i) x=k i)

theorem one_tuple_cell_mass {q:Format} (Y:OneSilhouette p N r)
    (t:Tagging p (Messenger q)) (z:Messenger q→F) (k:Messenger q→Fin r)
    {η:ℝ} (hη:0≤η) (hk:∀ i,η≤oneWisp p Y (t i) (z i) (k i))
    (hN:2*num (Messenger q×Toast p)+2≤(N:ℝ))
    (herr:2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2)≤η^Fintype.card (Messenger q)/2):
    η^Fintype.card (Messenger q)/2≤pr (oneLawNu p N t z) (oneTupleCell Y t z k) := by
  let f i:Wgt (OneAtomKey (p:=p) (t i) N):=fun x=>ind (Y (t i) (z i) x=k i)
  have he:=one_reference_product t z f
    (fun i x=>(abs_of_nonneg (ind_nonneg _)).trans_le (ind_le_one _)) hN
  have hp:η^Fintype.card (Messenger q)≤∏ i,avg (oneLawOmega p N (t i) (z i)) (f i):=by
    rw [show η^Fintype.card (Messenger q)=∏ _i:Messenger q,η from by simp]
    apply Finset.prod_le_prod (fun _ _=>hη)
    intro i _
    have hh:=hk i
    change η≤mapW _ _ _ at hh
    exact hh
  have hprod:prodW f=fun x=>ind (oneTupleCell Y t z k x):=by
    funext x
    exact (ind_all (fun i=>Y (t i) (z i) (x i)=k i)).symm
  rw [hprod] at he
  have hleft:=(abs_le.mp he).1
  change -_≤pr (oneLawNu p N t z) (oneTupleCell Y t z k)-_ at hleft
  linarith only [hp,hleft,herr]

end
end Lax793645Proofs.Simplifications
