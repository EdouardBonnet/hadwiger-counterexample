import Lax793645Proofs.Simplifications.SupportLowerBounds
import Lax793645Proofs.Simplifications.OneStatusAtomBounds

/-! Support indicators, multiplied by a fixed atom height, define bounded query surrogates. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace OneQuill
variable {p : Shape} {n N r : ℕ} {q : Format} {d : Rates} {b : Bool}
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : OneUnit p n N) (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)

def oneSupportSeraph (θ : ℝ) (i : Messenger q) : Wgt (OneAtomKey (p:=p) (t i) N):=
  fun x=>supportLower θ (oneSeraph w t z o m s Y i x)
def oneSupportMirror (θ : ℝ) : Wgt (OneKeys t N):=
  fun x=>oneKappa (w.pen t)*prodW (oneSupportSeraph w t z o m s Y θ) x
def oneSupportSheen (θ : ℝ) (W : Wgt (OneKeys t N)) : ℝ:=
  avg (oneLawNu p N t z) (fun x=>oneSupportMirror w t z o m s Y θ x*W x)

theorem one_support_mirror_bound (θ : ℝ) (hθ : 0≤θ ∧ θ≤1) (x : OneKeys t N) :
    0≤oneSupportMirror w t z o m s Y θ x ∧
      oneSupportMirror w t z o m s Y θ x≤1 := by
  have hi i y : 0≤oneSupportSeraph w t z o m s Y θ i y ∧
      oneSupportSeraph w t z o m s Y θ i y≤1:=support_lower_bounds θ _ hθ
  have hp : 0≤prodW (oneSupportSeraph w t z o m s Y θ) x:=
    prodW_nonneg (fun i y=>(hi i y).1) x
  have ht : prodW (oneSupportSeraph w t z o m s Y θ) x≤1:=by
    simpa only [prodW,prod_const_one] using Finset.prod_le_prod
      (s:=univ) (g:=fun _ : Messenger q=>(1:ℝ))
      (fun i _=>(hi i (x i)).1) (fun i _=>(hi i (x i)).2)
  exact ⟨mul_nonneg (one_kappa_pos _).le hp,
    (mul_le_mul (one_kappa_top w t) ht hp zero_le_one).trans_eq (one_mul _)⟩


end OneQuill

end
end Lax793645Proofs.Simplifications
