import Lax342547.FingerprintCounts
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic

namespace Lax342547Proofs.FingerprintCounts
open Lax342547.FingerprintCounts

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.FingerprintCounts.pad_recovers
---
-/
theorem pad_recovers {U : Type} (L : ℕ) (l : List U) : (pad L l).filterMap id = l := by
  simp [pad,List.filterMap_map]

/--
---
conclusion: Lax342547.FingerprintCounts.pad_injective
---
-/
theorem pad_injective {U : Type} (L : ℕ) : Function.Injective (pad (U := U) L) := by
  intro a b h
  have hh := congrArg (List.filterMap id) h
  simpa only [pad_recovers] using hh

/--
---
conclusion: Lax342547.FingerprintCounts.pad_length
---
-/
theorem pad_length {U : Type} (L : ℕ) (l : List U) (hl : l.length ≤ L) : (pad L l).length = L := by
  simp [pad,Nat.add_sub_of_le hl]

/--
---
conclusion: Lax342547.FingerprintCounts.bounded_list_count
---
-/
theorem bounded_list_count {U : Type} [Fintype U] (T : Finset (List U)) (L : ℕ)
    (hL : ∀ l ∈ T, l.length ≤ L) : T.card ≤ (Fintype.card U+1)^L := by
  classical
  let W := T.image (pad L)
  have hw : W.filter (fun l => l.length = L) = W := by
    apply Finset.filter_eq_self.mpr
    intro l hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    exact pad_length L a (hL a ha)
  have hh := Finset.card_filter_length_eq_le (T := W) (s := L)
  rw [hw] at hh
  have hc : W.card = T.card := Finset.card_image_of_injective T (pad_injective L)
  simpa only [hc,Fintype.card_option] using hh

end Lax342547Proofs.FingerprintCounts
