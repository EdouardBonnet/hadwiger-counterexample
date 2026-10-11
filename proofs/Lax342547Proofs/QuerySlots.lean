import Lax342547.QuerySlots

namespace Lax342547Proofs.QuerySlots
open Lax342547.QuerySlots

set_option backward.isDefEq.respectTransparency false
open Lax342547.CutProfiles
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.PairedWitnesses
open Lax342547.StarRouting

/--
---
conclusion: Lax342547.QuerySlots.incident_count
---
-/
theorem incident_count {k : ℕ} (l : Tag k) :
    Fintype.card {e : Component (Tag k) // l ∈ e.val} = 2 * k := by
  classical
  have h := Fintype.card_congr (incidentEquiv l)
  have hn : Fintype.card {t : Tag k // t ≠ l} = 2 * k := by
    simp [Fintype.card_subtype_compl, Tag, ZMod.card]
  rw [hn] at h
  exact h.symm

/--
---
conclusion: Lax342547.QuerySlots.position_count
---
-/
theorem position_count {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Fintype.card (Position W) = ∑ i : Fin 2, ∑ z : Fin 2, W.length i z := by
  simp [Position, Fintype.card_sigma]

/--
---
conclusion: Lax342547.QuerySlots.position_budget
---
-/
theorem position_budget {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Fintype.card (Position W) ≤ 28 := by
  rw [Lax342547.QuerySlots.position_count]
  calc
    _ ≤ ∑ _ : Fin 2, ∑ _ : Fin 2, 7 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun z _ => W.short i z)
    _ = 28 := by norm_num

/--
---
conclusion: Lax342547.QuerySlots.slot_count
---
-/
theorem slot_count {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Fintype.card (Slot W) = Fintype.card (Position W) * (4 * k) := by
  classical
  simp [Slot, Position, Fintype.card_sigma, Lax342547.QuerySlots.incident_count, Nat.mul_assoc]
  omega

/--
---
conclusion: Lax342547.QuerySlots.slot_budget
---
-/
theorem slot_budget {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Fintype.card (Slot W) ≤ 56 * (Fintype.card (Tag k) - 1) := by
  rw [Lax342547.QuerySlots.slot_count]
  have h := Nat.mul_le_mul_right (4 * k) (Lax342547.QuerySlots.position_budget W)
  simp only [Tag, ZMod.card, Nat.add_sub_cancel] 
  nlinarith [h]

end Lax342547Proofs.QuerySlots
