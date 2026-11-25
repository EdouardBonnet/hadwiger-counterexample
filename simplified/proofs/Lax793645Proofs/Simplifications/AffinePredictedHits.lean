import Lax793645Proofs.Simplifications.AffineQueryLoss
import Lax793645Proofs.Simplifications.PredictedRareEvents

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Function
open scoped BigOperators Topology
noncomputable section

theorem affine_rejection_vanish (p : Shape) (K positions : ℕ) :
    Tendsto (fun n : ℕ => bp ((positions : ℝ)+baseProtectionDim p K-(n : ℝ)))
      atTop (𝓝 0) := by
  simpa only [mul_zero,neg_one_mul,sub_eq_add_neg,bp_add] using
    (bp_nat_vanish (by norm_num : (0 : ℝ)<1)).const_mul
      (bp ((positions : ℝ)+baseProtectionDim p K))

namespace AffineOptions
variable {p : Shape} {n N : ℕ} {q : Format} {d : Rates} {side : Bool}

/-- Uniform prediction and rejection errors reduce the fixed hit threshold.
They are never subtracted from the mass of the compatible leaf pairs. -/
theorem predicted_qualify_hit (w : Quill p q d side) (t : Tagging p (Messenger q))
    (z : Messenger q → F) (s : Charts p n d) (m : Mixer p n) (K : ℕ)
    (pin : Pin p n N) (μ : Wgt (UnitType p n N)) (P : UnitType p n N → Prop)
    (α : Party) (g : Bool → Augur p N) (ε : ℝ)
    (E H : Keys (p:=p) t N → Prop) (hHE : ∀ x,H x → E x)
    {a h : ℝ} (hh : 0 < h)
    (hq : w.predictedQualified t z s m K μ P a α g ε E)
    (hμ : IsLaw μ) (hw : w.moral t z) (hr : 1 ≤ p.r) (hn : 2*p.r ≤ n)
    (hpen : affinePenSpace (w.pen t) pin.sp (affineQorth K) K)
    (herr : Fintype.card (Messenger q)*((scanPrice p)⁻¹*ε) ≤ h)
    (hreject : bp (num (Messenger q)+(baseProtectionDim p K : ℝ)-(n : ℝ)) ≤ a*h)
    (hbad : pr μ (fun o => ¬w.baseSober t z K H m (4*h) o) ≤ a) :
    a*h ≤ pr (sales w t z pin K μ P m s) H := by
  have hfull := w.predicted_qualify_hit t z s m K μ P α g ε E H hHE
    (h:=2*h) (by positivity) hq hμ hw hr hn (herr.trans (by linarith))
    (by simpa only [show 2*(2*h)=4*h from by ring] using hbad)
  have hmass := (affine_sales_rejection w t z pin K μ P m s hμ.sub hw hr hn hpen).2
  have hgap := (var_pr (w.sales t z μ P m s) (sales w t z pin K μ P m s) H).trans hmass
  nlinarith only [hfull,hgap,hreject]

end AffineOptions
end
end Lax793645Proofs.Simplifications
