import Lax342547.PairedKeys
import Lax342547Proofs.KeySpans
import Lax342547Proofs.PairedWitnesses

namespace Lax342547Proofs.PairedKeys

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.PairedRecipes Lax342547.PairedKeys
open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.NominalPrimal Lax342547.KeySpans

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

theorem position_count (W : Lists k n b degree r hr) : Fintype.card (Positions W) ≤ 28 := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _i : Fin 2, 14 := Finset.sum_le_sum (fun i _ => (PairedWitnesses.list_budgets W).1 i)
    _ = 28 := by simp

theorem keys_le_rays (W : Lists k n b degree r hr) (e : Component (Tag k)) :
    keys (H := H) W e ≤ Submodule.span Binary (Set.range (ray (H := H) (labels W) (bases W))) := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  by_cases he : (W.left x.1 x.2.1 x.2.2).tag ∈ e.val
  · simp only [direction, he, if_pos]
    exact Submodule.subset_span ⟨x, rfl⟩
  · simp only [direction, he]
    exact Submodule.zero_mem _

/--
---
conclusion: Lax342547.PairedKeys.key_bounds
---
There are at most fourteen selected atoms at each of the two endpoints.
Each incident ray has zero channel coordinates. Their span therefore
lies in the primal space and has dimension at most twenty-eight.
-/
theorem key_bounds [Fintype H] (W : Lists k n b degree r hr) (e : Component (Tag k)) :
    keys (H := H) W e ≤ primal ∧ Module.finrank Binary (keys (H := H) W e) ≤ 28 := by
  classical
  constructor
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    by_cases he : (W.left x.1 x.2.1 x.2.2).tag ∈ e.val
    · simp only [direction, he, if_pos]
      intro i h
      simp [ray, primalEmbedding]
    · simp only [direction, he]
      exact Submodule.zero_mem _
  · exact (finrank_range_le_card (R := Binary) (direction (H := H) W e)).trans (position_count W)

theorem left_fresh_spans [Fintype H]
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i) (a : Component (Tag k) × Bool) :
    Disjoint (tableSpace P a) (keys (H := H) W a.1) := by
  have h := KeySpans.span_disjoint P A hA (labels W) (bases W) W.left_fresh
    (fun i => (PairedWitnesses.list_budgets W).1 i) (fun i x => hfresh i x.1 x.2) a
  exact h.mono_right (keys_le_rays W a.1)

/--
---
conclusion: Lax342547.PairedKeys.fresh_spans
---
Indexed sparse exclusion shows that even the span of all selected rays
is disjoint from the table. The component's incident key span is a
subspace of that span. Apply the same argument after reversing the units.
-/
theorem fresh_spans [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A B : Fin 2 → Finset (Fin b → Binary)) (hA : Excludes P A) (hB : Excludes Q B)
    (hfresh : FreshAgainst W A B) :
    (∀ a, Disjoint (tableSpace P a) (keys (H := H) W a.1)) ∧
      ∀ a, Disjoint (tableSpace Q a) (keys (H := H) (flip W) a.1) := by
  exact ⟨fun a => left_fresh_spans W P A hA hfresh.1 a,
    fun a => left_fresh_spans (flip W) Q B hB (fun i z t => hfresh.2 z i t) a⟩

end Lax342547Proofs.PairedKeys
