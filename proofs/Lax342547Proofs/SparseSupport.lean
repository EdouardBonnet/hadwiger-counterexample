import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! A small-dimensional space cannot contain sparse vectors using many labels,
provided the encoding has no kernel vector at the comparison sparsity. -/

namespace Lax342547Proofs.SparseSupport

variable {K Label M V : Type} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup V] [Module K V]

set_option backward.isDefEq.respectTransparency false in
theorem exists_support_bound (F : (Label →₀ M) →ₗ[K] V)
    (U : Submodule K V) [Module.Finite K U] {k l : ℕ}
    (hdim : Module.finrank K U ≤ k)
    (hker : ∀ c : Label →₀ M, c.support.card ≤ (k + 1) * l → F c = 0 → c = 0) :
    ∃ B : Finset Label, B.card ≤ k * l ∧
      ∀ c : Label →₀ M, c.support.card ≤ l → F c ∈ U → c.support ⊆ B := by
  classical
  let S : Set U := {v | ∃ c : Label →₀ M, c.support.card ≤ l ∧ F c = v.val}
  obtain ⟨T, hTS, hspan, hlin⟩ := exists_linearIndependent K S
  let : Finite T := hlin.finite
  let : Fintype T := Fintype.ofFinite T
  have hcard : Fintype.card T ≤ k := hlin.fintype_card_le_finrank.trans hdim
  have hsparse (t : T) : ∃ c : Label →₀ M, c.support.card ≤ l ∧ F c = t.val.val :=
    hTS t.property
  choose c hc hFc using hsparse
  let B : Finset Label := Finset.univ.biUnion (fun t : T => (c t).support)
  have hB : B.card ≤ k * l := calc
    B.card ≤ ∑ t : T, (c t).support.card := Finset.card_biUnion_le
    _ ≤ ∑ _t : T, l := Finset.sum_le_sum (fun t _ => hc t)
    _ = Fintype.card T * l := by simp
    _ ≤ k * l := Nat.mul_le_mul_right l hcard
  refine ⟨B, hB, ?_⟩
  intro d hd hdU
  let v : U := ⟨F d, hdU⟩
  have hvS : v ∈ S := ⟨d, hd, rfl⟩
  have hv : v ∈ Submodule.span K (Set.range (fun t : T => (t : U))) := by
    rw [Subtype.range_coe_subtype]
    change v ∈ Submodule.span K T
    rw [hspan]
    exact Submodule.subset_span hvS
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  let d' : Label →₀ M := ∑ t : T, a t • c t
  have hFd : F d' = F d := by
    have he := congrArg (fun x : U => (x : V)) ha
    simpa only [d', map_sum, map_smul, hFc, Submodule.coe_sum,
      Submodule.coe_smul] using he
  have hd' : d'.support ⊆ B := by
    intro s hs
    by_contra hn
    apply (Finsupp.mem_support_iff.mp hs)
    change (∑ t : T, a t • c t) s = 0
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro t _
    have hst : s ∉ (c t).support := fun ht =>
      hn (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, ht⟩)
    simp [Finsupp.notMem_support_iff.mp hst]
  have hdiff : (d - d').support ⊆ d.support ∪ B := by
    intro s hs
    by_contra hn
    have hns : s ∉ d.support := fun h => hn (Finset.mem_union_left _ h)
    have hns' : s ∉ d'.support := fun h => hn (Finset.mem_union_right _ (hd' h))
    exact (Finsupp.mem_support_iff.mp hs) (by
      simp [Finsupp.notMem_support_iff.mp hns, Finsupp.notMem_support_iff.mp hns'])
  have hdiffcard : (d - d').support.card ≤ (k + 1) * l := calc
    _ ≤ (d.support ∪ B).card := Finset.card_le_card hdiff
    _ ≤ d.support.card + B.card := Finset.card_union_le _ _
    _ ≤ l + k * l := Nat.add_le_add hd hB
    _ = (k + 1) * l := by simp [Nat.add_mul, Nat.add_comm]
  have heq : d = d' := sub_eq_zero.mp (hker _ hdiffcard (by rw [map_sub, hFd, sub_self]))
  rw [heq]
  exact hd'

end Lax342547Proofs.SparseSupport
