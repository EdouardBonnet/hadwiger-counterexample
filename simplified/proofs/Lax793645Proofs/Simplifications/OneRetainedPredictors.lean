import Lax793645Proofs.Simplifications.OnePredictorCells
import Lax793645Proofs.Simplifications.OnePredictedDualEvaluation
import Lax793645Proofs.Simplifications.RetainedPredictors

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis PredictionClass
open Finset Matrix Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N r:ℕ} {A B:Rates}

/-- The scalar system uses every attained predictor pair. The constant
η is a lower mass certificate for all of them, so no cell is dropped. -/
theorem one_attained_scalar_soluble (g : Bool→OneAugur p N) (α : Party)
    (c : PredictionClass) (hc : oneFiniteClass g α=c) {R : ℕ} (hrows : OneAlgebraicRows g R)
    (X : ∀ i,Cell (A i)) (Z : ∀ i,Cell (B i)) (η : ℝ)
    (hmass : ∀ l q x, η≤oneWisp p (onePredictorPartition c g) l q
      (onePredictorPartition c g l q x))
    (m : OneUnit p n N→Bool→Profile p n)
    (x y : OneUnit p n N) (T : OneCross p n) (s : Charts p n A) (t : Charts p n B)
    (hx : oneCoordSpec m x s X) (hy : oneCoordSpec m y t Z) (hg : 3≤p.g)
    (he : glint p (m x)=glint p (m y))
    (hcompat : c.compatible α (glint p (m x)) (oneCardTone m x T,
      oneCardTone m y (fun e=>(T e)ᵀ))) :
    scorecard (fun i => predictedSpan (α i.1) (α i.2) (X i.1) (Z i.2)
      (retainedPatterns (oneWisp p (onePredictorPartition c g)) (predictorPulse c) η i))
      (oneHailing s t T) := by
  classical
  let Y:=onePredictorPartition c g
  let v : PredictionData p A B predictorCellCount:=⟨α,predictorPulse c,X,Z⟩
  let l₀ : Tag p.g:=⟨0,by omega⟩
  let available := retainedPatterns (oneWisp p Y) (predictorPulse c) η
  have hat (i : Grid) (l : Tag p.g) (q : F) (k : OneAtomKey (p:=p) l N) :
      (q,onePreparedPredictor c g i.1 l q k,onePreparedPredictor c g i.2 l q k)∈available i := by
    refine ⟨l,Y l q k,hmass l q k,?_,?_⟩ <;>
      exact (congrFun (congrFun (congrFun (one_predictor_pulse_eq c g _) l) q) k).symm
  have hcover i := predicted_covers (α i.1) (α i.2) (X i.1) (Z i.2) (available i)
    (fun q=>⟨_,_,hat i l₀ q 0⟩)
  by_contra h
  obtain ⟨z,hz,hlaw,hbad⟩:=jargon_score _ _ h hcover
  obtain ⟨hbase,hhead,hrelation⟩:=predicted_dual_coefficients α X Z available
    (fun i=>⟨_,hat i l₀ 0 0⟩) z hlaw
  have hrel i l q k := hrelation i _ (hat i l q k)
  have hsame i l q k : onePreparedPredictor c g i l q k=onePreparedPredictor c g i l 0 k := by
    by_cases hd : c=dusk
    · simp [onePreparedPredictor,hd]
    · simpa only [onePreparedPredictor,if_neg hd] using hrows.sameSlice i l q k
  have hgamma i : z.gam i=0 := by
    have h₀ := hrel i l₀ 0 0
    have h₁ := hrel i l₀ 1 0
    dsimp only at h₀ h₁
    rw [mul_one,hsame _ _ 1 _,hsame _ _ 1 _] at h₁
    rw [mul_zero] at h₀
    exact h₁.symm.trans h₀
  apply hbad
  apply one_exact_harmony v c m x y T s t hx hy (hc ▸ one_finite_lit g α)
    he hcompat z hz hbase hhead hgamma
  intro hd i j
  rw [←hc]
  apply one_finite_echoes g α i j (z.left j) (z.right i) (z.gam (i,j))
    ((hhead (i,j)).1.symm.trans (hhead (i,j)).2)
  intro l q k
  simpa only [oneAssembly,onePreparedPredictor,if_neg hd] using hrel (i,j) l q k

end
end Lax793645Proofs.Simplifications
