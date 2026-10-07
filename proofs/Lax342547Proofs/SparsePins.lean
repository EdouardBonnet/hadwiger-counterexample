import Lax342547.SparsePins
import Lax342547Proofs.SparseSupport
import Lax342547Proofs.SelectorInterpolation

namespace Lax342547Proofs.SparsePins

open Lax342547.MomentSpace Lax342547.SparsePins

set_option backward.isDefEq.respectTransparency false in
theorem expansion_apply {Label Coord Base : Type} (p : Label → Coord → Binary)
    (c : Label →₀ (Base → Binary)) (i : Coord × Base) :
    expansion p c i = ∑ s ∈ c.support, p s i.1 * c s i.2 := by
  simp only [expansion, Finsupp.lsum_apply, Finsupp.sum, Finset.sum_apply, labelTensor,
    LinearMap.coe_mk, AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in
theorem eq_zero_of_expansion_eq_zero {Base : Type} {b degree : ℕ}
    (c : (Fin b → Binary) →₀ (Base → Binary))
    (hcard : c.support.card ≤ degree + 1)
    (hzero : expansion (selectorEval (degree := degree)) c = 0) : c = 0 := by
  classical
  have hlin := SelectorInterpolation.selectorEval_linearIndependent (degree := degree)
    (fun s : c.support => s.val) Subtype.val_injective (by simpa only [Fintype.card_coe] using hcard)
  have hrel (x : Base) :
      ∑ s : c.support, c s.val x • selectorEval (degree := degree) s.val = 0 := by
    ext a
    have he := congrFun hzero (a, x)
    rw [expansion_apply] at he
    rw [Finset.sum_apply]
    change (∑ s : c.support, c s.val x * selectorEval s.val a) = 0
    exact (Finset.sum_coe_sort c.support (fun s => c s x * selectorEval s a)).trans
      (by simpa only [Pi.zero_apply, mul_comm] using he)
  ext s x
  by_cases hs : s ∈ c.support
  · exact (Fintype.linearIndependent_iff.mp hlin) (fun t => c t.val x) (hrel x) ⟨s, hs⟩
  · simp [Finsupp.notMem_support_iff.mp hs]

theorem one_space_labels {Base : Type} [Fintype Base] {b degree K l : ℕ}
    (U : Submodule Binary (SelectorCoordinates b degree × Base → Binary))
    (hdim : Module.finrank Binary U ≤ K)
    (hdegree : (K + 1) * l ≤ degree + 1) :
    ∃ B : Finset (Fin b → Binary), B.card ≤ K * l ∧
      ∀ c : (Fin b → Binary) →₀ (Base → Binary),
        c.support.card ≤ l → expansion (selectorEval (degree := degree)) c ∈ U →
        c.support ⊆ B := by
  apply SparseSupport.exists_support_bound _ U hdim
  intro c hc hzero
  exact eq_zero_of_expansion_eq_zero c (hc.trans hdegree) hzero

/--
---
conclusion: Lax342547.SparsePins.sparse_pin_labels
---
Choose independent sparse vectors spanning all sparse members of each
projected space, and collect their labels. Interpolation makes every
comparison with another sparse expansion unique, so that expansion has
no additional nonzero labels. The union over signs and components has
the required size.
-/
theorem sparse_pin_labels {Base Component : Type} [Fintype Base] [Fintype Component]
    {b degree K R : ℕ}
    (U : Bool → Component → Submodule Binary (SelectorCoordinates b degree × Base → Binary))
    (hdim : ∀ sign e, Module.finrank Binary (U sign e) ≤ K)
    (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ B : Finset (Fin b → Binary),
      B.card ≤ 2 * Fintype.card Component * K * (R + 14) ∧
      ∀ sign e (c : (Fin b → Binary) →₀ (Base → Binary)),
        c.support.card ≤ R + 14 → expansion (selectorEval (degree := degree)) c ∈ U sign e →
        c.support ⊆ B := by
  classical
  have each (i : Bool × Component) := one_space_labels (U i.1 i.2) (hdim i.1 i.2) hdegree
  choose B hB hcover using each
  refine ⟨Finset.univ.biUnion B, ?_, ?_⟩
  · calc
      (Finset.univ.biUnion B).card ≤ ∑ i : Bool × Component, (B i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i : Bool × Component, K * (R + 14) := Finset.sum_le_sum (fun i _ => hB i)
      _ = 2 * Fintype.card Component * K * (R + 14) := by
        simp [Fintype.card_prod, Nat.mul_assoc]
  · intro sign e c hc hcU s hs
    exact Finset.mem_biUnion.mpr ⟨(sign, e), Finset.mem_univ _, hcover _ c hc hcU hs⟩

theorem expansion_indicator {Label Coord Base : Type} (p : Label → Coord → Binary)
    (L : Finset Label) (z : Label → Base → Binary) :
    expansion p (Finsupp.indicator L (fun s _ => z s)) = ∑ s ∈ L, labelTensor p s (z s) := by
  change (Finsupp.indicator L (fun s _ => z s)).sum (fun s => labelTensor p s) = _
  exact Finsupp.sum_indicator_index z (fun s _ => (labelTensor p s).map_zero)

/-- The same uniform budget in the paper's finite-sum notation. Zero
coefficients and non-minimal choices of the finite label set are allowed. -/
theorem sparse_pin_labels_finset {Base Component : Type} [Fintype Base] [Fintype Component]
    {b degree K R : ℕ}
    (U : Bool → Component → Submodule Binary (SelectorCoordinates b degree × Base → Binary))
    (hdim : ∀ sign e, Module.finrank Binary (U sign e) ≤ K)
    (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ B : Finset (Fin b → Binary),
      B.card ≤ 2 * Fintype.card Component * K * (R + 14) ∧
      ∀ sign e (L : Finset (Fin b → Binary)) (z : (Fin b → Binary) → Base → Binary),
        L.card ≤ R + 14 →
        (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (z s)) ∈ U sign e →
        ∀ s ∈ L, z s ≠ 0 → s ∈ B := by
  obtain ⟨B, hB, hcover⟩ := sparse_pin_labels U hdim hdegree
  refine ⟨B, hB, ?_⟩
  intro sign e L z hL hz s hs hzs
  let c := Finsupp.indicator L (fun t _ => z t)
  have hc : c.support.card ≤ R + 14 :=
    (Finset.card_le_card (Finsupp.support_indicator_subset L _)).trans hL
  have hcU : expansion (selectorEval (degree := degree)) c ∈ U sign e := by
    rw [show c = Finsupp.indicator L (fun t _ => z t) from rfl, expansion_indicator]
    exact hz
  apply hcover sign e c hc hcU
  apply Finsupp.mem_support_iff.mpr
  simpa only [c, Finsupp.indicator_of_mem hs] using hzs

end Lax342547Proofs.SparsePins
