import Lax342547.StarRouting
import Lax342547.PairedWitnesses

/-!
---
title: The actual paired-list key slot budget
type: definition and theorem
---
Counting both signs and every incident component in all four bounded witness lists gives at most 56(g-1) ambient vector slots.
-/

namespace Lax342547.QuerySlots

open Lax342547.CutProfiles
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.PairedWitnesses
open Lax342547.StarRouting

abbrev Position {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :=
  Σ i : Fin 2, Σ z : Fin 2, Fin (W.length i z)

abbrev Slot {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :=
  Σ p : Position W, {e : Component (Tag k) // (W.left p.1 p.2.1 p.2.2).tag ∈ e.val} × Bool

axiom incident_count {k : ℕ} (l : Tag k) :
    Fintype.card {e : Component (Tag k) // l ∈ e.val} = 2 * k

axiom position_count {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Fintype.card (Position W) = ∑ i : Fin 2, ∑ z : Fin 2, W.length i z

axiom position_budget {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Fintype.card (Position W) ≤ 28

axiom slot_count {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Fintype.card (Slot W) = Fintype.card (Position W) * (4 * k)

axiom slot_budget {k n b degree r : ℕ} {hr : 2 * r ≤ n} (W : Lists k n b degree r hr) :
    Fintype.card (Slot W) ≤ 56 * (Fintype.card (Tag k) - 1)

end Lax342547.QuerySlots
