import Lax342547.BarredElimination
import Lax342547Proofs.SelectedBlocks
import Lax342547.PairedKeys
import Lax342547.PairedWitnesses
import Lax342547.SparseKeyCoefficients
import Lax342547Proofs.BarredSpaces

namespace Lax342547Proofs.BarredElimination

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces
open Lax342547.PinLabelExclusions Lax342547.BarredSpaces Lax342547.ResidualLabels
open Lax342547.NominalPrimal Lax342547.SparsePins

set_option backward.isDefEq.respectTransparency false

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

/--
---
conclusion: Lax342547.BarredElimination.individual_keys_zero
---
Expand the actual individual key span using its at most fourteen
generators. Sparse fresh coefficient extraction kills every base-vector
coefficient, including inactive generators, hence their entire sum.
-/
theorem individual_keys_zero {R : ℕ} (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Component (Tag k) × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R) (v : (Fin b → Binary) → Option (Base k n) → Binary)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (hfresh : ∀ z t, (W.left i z t).label ∉ A i)
    (q : Vector k n b degree) (hq : q ∈ individualKeys W i a.1)
    (hpin : (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) - q ∈ projected P i a) :
    q = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Binary).mp hq
  have hlift : (∑ u, c u • labelTensor (selectorEval (degree := degree))
      (W.left i u.1 u.2).label (Lax342547.SelectedBlocks.keyBase W i a.1 u)) = q := by
    simpa only [SelectedBlocks.key_lift] using hc
  have hcoeff := Lax342547.SparseKeyCoefficients.coefficients_zero P A hA i a L hL v
    (fun u : Σ z, Fin (W.length i z) => (W.left i u.1 u.2).label) (W.left_fresh i)
    (Lax342547.SelectedBlocks.keyBase W i a.1) ((Lax342547.PairedWitnesses.list_budgets W).1 i)
    (fun u => hfresh u.1 u.2) hdisjoint c (hlift ▸ hpin)
  rw [← hlift]
  apply Finset.sum_eq_zero
  intro u _
  rw [← map_smul, hcoeff u, map_zero]

theorem private_properties {B H : Type} (U : Fin 2 → Submodule Binary (H → Binary))
    (v : (Fin 2 × (B ⊕ H)) → Binary) (hv : v ∈ ⨆ i, (U i).map (channelEmbedding i)) :
    (∀ i, primalProjection i v = 0) ∧ (∀ i, channelProjection i v ∈ U i) := by
  constructor
  · intro i
    have hle : (⨆ j, (U j).map (channelEmbedding (B := B) j)) ≤ LinearMap.ker (primalProjection i) := by
      apply iSup_le
      intro j
      rintro _ ⟨w, hw, rfl⟩
      ext c
      simp [primalProjection, channelEmbedding]
    exact hle hv
  · intro i
    have hle : (⨆ j, (U j).map (channelEmbedding (B := B) j)) ≤
        (U i).comap (channelProjection i) := by
      apply iSup_le
      intro j
      rintro _ ⟨w, hw, rfl⟩
      change channelProjection i (channelEmbedding j w) ∈ U i
      by_cases hji : j = i
      · subst j
        simpa [channelProjection, channelEmbedding] using hw
      · have hz : channelProjection i (channelEmbedding (B := B) j w) = 0 := by
          ext h
          simp [channelProjection, channelEmbedding, Ne.symm hji]
        rw [hz]
        exact Submodule.zero_mem _
    exact hle hv

/--
---
conclusion: Lax342547.BarredElimination.private_primal_pin
---
A primal vector has zero channel projections. In its pin/private
decomposition those projections lie in complementary protected and
private spaces, so both vanish; the channel-supported private vector
is zero and the original vector is in the pin.
-/
theorem private_primal_pin {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Comp × Bool)
    (hU : ∀ i, IsCompl (protectedChannel P i a) (U i))
    (v : (Fin 2 × (B ⊕ H)) → Binary) (hv : v ∈ primal)
    (h : v ∈ P.space a ⊔ ⨆ i, (U i).map (channelEmbedding i)) :
    v ∈ P.space a := by
  obtain ⟨p, hp, t, ht, hpt⟩ := Submodule.mem_sup.mp h
  have hprivate := private_properties U t ht
  have hvchan (i : Fin 2) : channelProjection i v = 0 := by
    ext h
    exact hv i h
  have htchan (i : Fin 2) : channelProjection i t = 0 := by
    have hpchan : channelProjection i p ∈ protectedChannel P i a :=
      Submodule.mem_map.mpr ⟨p, hp, rfl⟩
    have he : channelProjection i p + channelProjection i t = 0 := by
      rw [← map_add, hpt, hvchan]
    have hpU : channelProjection i p ∈ U i := by
      have heq : channelProjection i p = -channelProjection i t := eq_neg_of_add_eq_zero_left he
      rw [heq]
      exact (U i).neg_mem (hprivate.2 i)
    have hpzero := Submodule.disjoint_def.mp (hU i).disjoint _ hpchan hpU
    simpa only [hpzero, zero_add] using he
  have htzero : t = 0 := by
    ext ⟨i, c | h⟩
    · exact congrFun (hprivate.1 i) c
    · exact congrFun (htchan i) h
  have hpv : p = v := by simpa [htzero] using hpt
  exact hpv ▸ hp

/--
---
conclusion: Lax342547.BarredElimination.sparse_barred
---
Project a barred decomposition onto each primal endpoint. Private
channels project to zero, and unselected sparse supports force both
projected key vectors to vanish. Keys have no channels, hence the
nominal key vector is zero. Protected/private complementarity then
reduces the remaining decomposition to a pin vector.
-/
theorem sparse_barred {R : ℕ} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Component (Tag k) × Bool)
    (hU : ∀ i, IsCompl (protectedChannel P i a) (U i))
    (L : Fin 2 → Finset (Fin b → Binary)) (hL : ∀ i, (L i).card ≤ R)
    (hdisjoint : ∀ i, Disjoint (L i) (chosenLabels W i))
    (c : Fin 2 → (Fin b → Binary) → Option (Base k n) → Binary)
    (v : (Fin 2 × (Coordinate k n b degree ⊕ H)) → Binary) (hv : v ∈ primal)
    (hvec : ∀ i, primalProjection i v = ∑ s ∈ L i, labelTensor selectorEval s (c i s))
    (h : v ∈ barred W P U a) : v ∈ P.space a := by
  obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.mp h
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hw
  have hrepr : v = p + q + t := by rw [← hpq] at hwt; exact hwt.symm
  have hprivate := private_properties U t ht
  have hqzero (i : Fin 2) : primalProjection i q = 0 := by
    apply Lax342547.BarredElimination.individual_keys_zero W P A hA i a (L i) (hL i) (c i) (hdisjoint i) (hfresh i)
      (primalProjection i q)
    · exact BarredSpaces.projected_keys W i a.1 (Submodule.mem_map.mpr ⟨q, hq, rfl⟩)
    · rw [← hvec, hrepr, map_add, map_add, hprivate.1 i, add_zero, add_sub_cancel_right]
      exact Submodule.mem_map.mpr ⟨p, hp, rfl⟩
  have hqprimal := (Lax342547.PairedKeys.key_bounds (H := H) W a.1).1 hq
  have hq0 : q = 0 := by
    ext ⟨i, d | h⟩
    · exact congrFun (hqzero i) d
    · exact hqprimal i h
  apply Lax342547.BarredElimination.private_primal_pin P U a hU v hv
  rw [hrepr, hq0, add_zero]
  exact Submodule.mem_sup.mpr ⟨p, hp, t, ht, rfl⟩

end Lax342547Proofs.BarredElimination
