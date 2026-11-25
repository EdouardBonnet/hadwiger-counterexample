import Lax793645Proofs.Simplifications.OneNaturalScores
import Lax793645Proofs.Simplifications.OneLightQueryBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem uniform_weights_instances {A:Type} (i j:Fintype A) (P:A→Prop):
    @unifOn A i P=@unifOn A j P := by
  cases Subsingleton.elim i j
  rfl

theorem one_rejection_vanish (p:Shape) (K positions:ℕ):
    Tendsto (fun n:ℕ=>bp ((positions:ℝ)+oneBaseProtectionDim p K-(n:ℝ))) atTop (𝓝 0) := by
  simpa only [mul_zero,neg_one_mul,sub_eq_add_neg,bp_add] using
    (bp_nat_vanish (by norm_num:(0:ℝ)<1)).const_mul (bp ((positions:ℝ)+oneBaseProtectionDim p K))

namespace OneQuill
variable {p:Shape} {n N:ℕ} {q:Format} {d:Rates} {b:Bool}

theorem one_natural_sales_support (w:Quill p q d b) (t:Tagging p (Messenger q))
    (z:Messenger q→F) (μ:Wgt (OneUnit p n N)) (P:OneUnit p n N→Prop)
    (m:Mixer p n) (s:Charts p n d):
    lsupp (oneNaturalSales w t z μ P m s) (oneLawNu p N t z) := by
  intro k hk
  let E:=oneQueryCoordinateEquiv t N
  have hs:=one_sales_support w t z μ P m s (E.symm k)
  have href : mapW (oneLawNu p N t z) E.symm=unifOn (oneOwnPart (N:=N) t z):=
    (one_reference_coordinates t z).trans (uniform_weights_instances _ _ _)
  have hh:=congrFun href (E.symm k)
  rw [mapW_equiv_val,Equiv.symm_symm,Equiv.apply_symm_apply] at hh
  rw [hh]
  apply hs
  simpa only [oneNaturalSales,mapW_equiv_val] using hk

end OneQuill
end
end Lax793645Proofs.Simplifications
