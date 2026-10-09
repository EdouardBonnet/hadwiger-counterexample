import Lax342547.RawLaw
import Mathlib.Tactic.Ring

namespace Lax342547Proofs.RawLaw

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.RawLaw
open scoped ENNReal

variable {B H N Comp : Type} [Fintype B] [Fintype H] [Fintype N] [Fintype Comp]
variable [DecidableEq Comp]

theorem frame_card_bound (E : Matrix B B Binary) :
    Fintype.card (Frame B H N E) ≤
      2 ^ (2 * Fintype.card N * (Fintype.card B + Fintype.card H)) := by
  classical
  have h := Fintype.card_le_of_injective _ (frameData_injective (E := E) (H := H) (N := N))
  have hdata : Fintype.card (FrameData (B := B) (H := H) (N := N)) =
      Fintype.card ((N → B → Binary) × (N → B → Binary) × (N → H → Binary) ×
        (N → H → Binary)) := Fintype.card_congr (Equiv.refl _)
  calc
    Fintype.card (Frame B H N E) ≤ Fintype.card (FrameData (B := B) (H := H) (N := N)) := h
    _ = _ := by
      rw [hdata]
      simp only [Fintype.card_prod, Fintype.card_fun, Binary, ZMod.card,
        ← pow_mul, ← pow_add]
      congr 1
      ring

/--
---
conclusion: Lax342547.RawLaw.raw_card_bound
---
Forget the Gram and injectivity constraints and count the four binary
matrices at every component. Each component uses 2N(d+h) bits.
-/
theorem raw_card_bound (E : Matrix B B Binary) :
    Fintype.card (Comp → Frame B H N E) ≤
      2 ^ (2 * Fintype.card Comp * Fintype.card N * (Fintype.card B + Fintype.card H)) := by
  rw [Fintype.card_fun]
  calc
    _ ≤ (2 ^ (2 * Fintype.card N * (Fintype.card B + Fintype.card H))) ^ Fintype.card Comp :=
      Nat.pow_le_pow_left (frame_card_bound E) _
    _ = _ := by rw [← pow_mul]; congr 1; ring

theorem uniformLaw_apply (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (o : Comp → Frame B H N E) :
    uniformLaw E o = (Fintype.card (Comp → Frame B H N E) : ℝ≥0∞)⁻¹ :=
  PMF.uniformOfFintype_apply o

/--
---
conclusion: Lax342547.RawLaw.uniformLaw_product
---
The cardinality of the function space is the product of the cardinalities
of the component spaces. Its uniform mass therefore factors exactly as
the product of the component uniform masses.
-/
theorem uniformLaw_product (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (o : Comp → Frame B H N E) :
    uniformLaw E o = ∏ e, PMF.uniformOfFintype (Frame B H N E) (o e) := by
  simp [uniformLaw_apply, PMF.uniformOfFintype_apply, ENNReal.inv_pow]

end Lax342547Proofs.RawLaw
