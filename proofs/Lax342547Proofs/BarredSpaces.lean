import Lax342547.BarredSpaces
import Lax342547.PairedAnnihilators
import Lax342547.PairedWitnesses
import Lax342547.ProjectedPins

namespace Lax342547Proofs.BarredSpaces

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.PairedWitnesses Lax342547.PairedKeys
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces
open Lax342547.PairedAnnihilators Lax342547.BarredSpaces

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

/--
---
conclusion: Lax342547.BarredSpaces.individual_key_dimension
---
Each endpoint contributes its two lists, of length at most seven each.
Restricting to incident atoms cannot enlarge their fourteen-vector span.
-/
theorem individual_key_dimension (W : Lists k n b degree r hr) (i : Fin 2)
    (e : Component (Tag k)) : Module.finrank Binary (individualKeys W i e) ≤ 14 := by
  exact (finrank_range_le_card (R := Binary) (individualDirection W i e)).trans
    ((Lax342547.PairedWitnesses.list_budgets W).1 i)

theorem projected_keys (W : Lists k n b degree r hr) (i : Fin 2)
    (e : Component (Tag k)) :
    (keys (H := H) W e).map (primalProjection i) ≤ individualKeys W i e := by
  classical
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨j, z, t⟩, rfl⟩
  change primalProjection i (direction (H := H) W e ⟨j, z, t⟩) ∈ individualKeys W i e
  by_cases he : (W.left j z t).tag ∈ e.val
  · by_cases hj : j = i
    · subst j
      have hv : primalProjection i (direction (H := H) W e ⟨i, z, t⟩) =
          individualDirection W i e ⟨z, t⟩ := by
        ext c
        simp [direction, he, individualDirection, Lax342547.KeySpans.ray, labels, bases,
          Lax342547.WitnessAtoms.PointAtom.vector, primalProjection, primalEmbedding]
      rw [hv]
      exact Submodule.subset_span ⟨⟨z, t⟩, rfl⟩
    · have hz : primalProjection i (direction (H := H) W e ⟨j, z, t⟩) = 0 := by
        ext c
        simp [direction, he, Lax342547.KeySpans.ray, primalProjection, primalEmbedding,
          Ne.symm hj]
      rw [hz]
      exact Submodule.zero_mem _
  · simp only [direction, he, if_false, map_zero]
    exact Submodule.zero_mem _

/--
---
conclusion: Lax342547.BarredSpaces.barred_projection
---
Pins project into their stored primal projections, keys project into
the endpoint's selected rays, and every private channel projects to zero.
-/
theorem barred_projection (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Component (Tag k) × Bool) (i : Fin 2) :
    (barred W P U a).map (primalProjection i) ≤ projected P i a ⊔ individualKeys W i a.1 := by
  rw [barred, Submodule.map_sup, Submodule.map_sup]
  apply sup_le
  · exact sup_le le_sup_left ((projected_keys W i a.1).trans le_sup_right)
  · rw [Submodule.map_iSup]
    apply iSup_le
    intro z
    rintro _ ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    have hz : primalProjection i (channelEmbedding (B := Coordinate k n b degree) z u) = 0 := by
      ext c
      simp [primalProjection, channelEmbedding]
    rw [hz]
    exact Submodule.zero_mem _

/--
---
conclusion: Lax342547.BarredSpaces.annihilator_component_rank
---
Project the paired pure annihilator to either individual primal quotient.
Each sign's quotient kernel is a projected pin of dimension at most K
plus at most fourteen selected rays. Sum the two kernel budgets.
-/
theorem annihilator_component_rank [Fintype H] {K : ℕ}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Fin 2 → Submodule Binary (H → Binary))
    (e : Component (Tag k)) (M : Fin 2 → Moment k n b degree)
    (h : PairedAnnihilates M (barred W P U (e, true)) (barred W P V (e, false))) :
    ∀ i, (M i).rank ≤ 2 * K + 28 := by
  intro i
  have hd (a : Component (Tag k) × Bool) :
      Module.finrank Binary ↥(projected P i a ⊔ individualKeys W i a.1) ≤ K + 14 := by
    have hp : Module.finrank Binary (projected P i a) ≤ K :=
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans
        (Lax342547.ProjectedPins.projected_rank P i)).trans hK
    have hk := Lax342547.BarredSpaces.individual_key_dimension W i a.1
    have hs := Submodule.finrank_sup_add_finrank_inf_eq (projected P i a) (individualKeys W i a.1)
    calc
      _ ≤ Module.finrank Binary ↥(projected P i a ⊔ individualKeys W i a.1) +
          Module.finrank Binary ↥(projected P i a ⊓ individualKeys W i a.1) := Nat.le_add_right _ _
      _ = Module.finrank Binary (projected P i a) + Module.finrank Binary (individualKeys W i a.1) := hs
      _ ≤ K + 14 := Nat.add_le_add hp hk
  have hr := Lax342547.PairedAnnihilators.endpoint_rank M _ _ h i
    (projected P i (e, true) ⊔ individualKeys W i e)
    (projected P i (e, false) ⊔ individualKeys W i e)
    (Lax342547.BarredSpaces.barred_projection W P U (e, true) i) (Lax342547.BarredSpaces.barred_projection W P V (e, false) i)
  calc
    _ ≤ _ := hr
    _ ≤ (K + 14) + (K + 14) := Nat.add_le_add (hd (e, true)) (hd (e, false))
    _ = 2 * K + 28 := by omega

end Lax342547Proofs.BarredSpaces
