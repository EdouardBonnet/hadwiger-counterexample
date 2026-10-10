import Lax342547.PureObstructions
import Lax342547Proofs.BarredSpaces
import Lax342547Proofs.LabelDecomposition
import Lax342547Proofs.SparseRepresentatives

namespace Lax342547Proofs.PureObstructions

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PairedAnnihilators Lax342547.BarredSpaces
open Lax342547.BaseMoments Lax342547.PureObstructions

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

theorem pureResponse_zero {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H)) : pureResponse D E 0 = 0 := by
  classical
  ext M
  simp [pureResponse, matrixPair]

/--
---
conclusion: Lax342547.PureObstructions.component_annihilation
---
Choose a parameter supported at one component. Every other response is
zero, so global annihilation tests every bilinear form at that component.
-/
theorem component_annihilation (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P U V x)
    (e : Component (Tag k)) :
    PairedAnnihilates (endpointComponent e x)
      (barred W P (U e) (e, true)) (barred W P (V e) (e, false)) := by
  classical
  intro β
  have hh := h (Pi.single e β)
  simp only [response, LinearMap.sum_apply, LinearMap.comp_apply] at hh
  rw [Finset.sum_eq_single e] at hh
  · simpa only [Pi.single_eq_same] using hh
  · intro f _ hfe
    rw [Pi.single_eq_of_ne hfe, pureResponse_zero, LinearMap.zero_apply]
  · simp

/--
---
conclusion: Lax342547.PureObstructions.component_rank
---
Apply the actual barred-space kernel budget to each endpoint and
component of the pair of cut profiles.
-/
theorem component_rank [Fintype H] {K : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P U V x) :
    ∀ i e, ((x i).val e).rank ≤ 2 * K + 28 := by
  intro i e
  exact BarredSpaces.annihilator_component_rank W P hK (U e) (V e) e
    (endpointComponent e x) (component_annihilation W P U V x h e) i

/--
---
conclusion: Lax342547.PureObstructions.component_labels
---
Actual cut components lie in the unrestricted Boolean moment span.
The proved component-rank bound supplies every hypothesis of the
low-rank label decomposition, including its sum-of-block-ranks bound.
-/
theorem component_labels [Fintype H] {K : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P U V x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) :
    ∀ i e, ∃ L : Finset (Fin b → Binary),
    ∃ Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary,
      L.card ≤ 2 * K + 28 ∧ (∀ s ∈ L, IsBaseMoment (Z s)) ∧
      (∑ s ∈ L, (Z s).rank) ≤ 2 * K + 28 ∧
      ∀ a c, (x i).val e a c = ∑ s ∈ L, selectorEval s a.1 * selectorEval s c.1 * Z s a.2 c.2 := by
  intro i e
  obtain ⟨w, hw⟩ := (x i).property
  have hm : (x i).val e ∈ momentSpace selectorEval Set.univ := by
    rw [← hw]
    exact SparseRepresentatives.cut_full_moment w e
  exact LabelDecomposition.low_rank_label_decomposition ((x i).val e) hm
    (component_rank W P hK U V x h i e) hdegree

end Lax342547Proofs.PureObstructions
