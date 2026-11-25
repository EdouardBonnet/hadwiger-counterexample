import Lax793645Proofs.Simplifications.OneRetainedPredictors
import Lax793645Proofs.Simplifications.OneOptionContracts
import Lax793645Proofs.Simplifications.OnePreparationConditions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix Finset Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p:Shape} {n N:ℕ}

theorem one_actual_tone (m:OneMarks p n N) (x y:OneUnit p n N)
    (hm:∀ i,m x i∈Xspace p n) (j:Bool):
    oneCardTone m x (oneCrossMatrix x y) j=
      joinPhase p (oneListens y) (unary j) (oneMarkedDelta x (m x)) := by
  unfold oneCardTone oneMarkedDelta
  rw [map_add,Fintype.sum_bool]
  simp_rw [one_lone_image,one_contract_actual x y _ j _ (hm _)]

theorem one_fits_tone (a b:ImagePlan (Comp p.g) (OneColumn p n))
    (ha:(onePinClosure p n).close a=a) (T U:OneCross p n)
    (m:OneMarks p n N) (x:OneUnit p n N) (h:oneFitsTable a b T U)
    (hx:∀ i,m x i∈oneEffectivePins (oneEndpointPrimalPins a) i) (j:Bool):
    oneCardTone m x T j=oneCardTone m x U j:=
  sum_congr rfl (fun i _=>one_fits_contract a b ha T U h i j _ (hx i))

end
end Lax793645Proofs.Simplifications
