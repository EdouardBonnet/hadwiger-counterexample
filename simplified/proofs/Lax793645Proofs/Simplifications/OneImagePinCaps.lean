import Lax793645Proofs.Simplifications.ImagePinCaps
import Lax793645Proofs.Simplifications.OneClosedPinLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

theorem one_pin_closure_bot : (onePinClosure p n).close ⊥=⊥ := by
  funext e
  change coordinateClosure (oneBlockCoordinates p n) ⊥=⊥
  simp [coordinateClosure,blockClosure]

/-- Arbitrary mixed endpoint image equations obey the same raw
exponential cap, with a factor six in the small error parameter. -/
theorem one_image_pin_cap (m : Mixer p n)
    (a : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    {ζ : ℝ} (hz : 0≤ζ) (hz' : ζ≤6)
    (hN : 2*dim (OneFull p n)+3≤N)
    (hζ : (dim (OneFull p n):ℝ)+2≤(ζ/6)*(2*N)) :
    pr (oneUnitRaw m N) (imagePinAgree oneCoordinateImages a)≤
      fee (2*N) ζ (imagePlanRank a.sp) := by
  apply image_pin_cap_of_closed oneCoordinateImages 6 (by omega) (onePinClosure p n)
    one_pin_closure_bot (oneUnitRaw m N) (prodW_nonneg (fun _=>one_raw_nonneg m)) ζ hz
    (fun b hb=>one_closed_pin_cap m b hb (by linarith) hN hζ) a

end
end Lax793645Proofs.Simplifications
