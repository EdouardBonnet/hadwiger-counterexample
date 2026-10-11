import Lax342547.CutSparsity
import Lax342547Proofs.CutProfiles
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.CutSparsity

noncomputable section

open Lax342547.MomentSpace Lax342547.CutProfiles Lax342547.CutSparsity

variable {Tag V : Type} [AddCommGroup V] [Module Binary V]

theorem pair_eq {i j k l : Tag} [DecidableEq Tag]
    (h : ({i, j} : Finset Tag) = {k, l}) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  apply Set.pair_eq_pair_iff.mp
  simpa using congrArg (fun s : Finset Tag => (s : Set Tag)) h

theorem add_ne_zero_iff (a b : V) : a + b ≠ 0 ↔ a ≠ b := by
  rw [← ZModModule.sub_eq_add, sub_ne_zero]

noncomputable def pairCut (w : Tag → V) (p : UnequalPairs w) : NonzeroCuts w := by
  classical
  have h : p.val.1 ≠ p.val.2 := fun he => p.property (congrArg w he)
  exact ⟨⟨{p.val.1, p.val.2}, Finset.card_pair h⟩,
    (CutProfiles.cutMap_pair w h).symm ▸ (add_ne_zero_iff _ _).2 p.property⟩

noncomputable def pairFlag (w : Tag → V) (p : UnequalPairs w) :
    Σ e : NonzeroCuts w, {t : Tag // t ∈ e.val.val} := by
  classical
  exact ⟨pairCut w p, ⟨p.val.1, by simp [pairCut]⟩⟩

theorem pairFlag_injective (w : Tag → V) : Function.Injective (pairFlag w) := by
  classical
  intro p q h
  have he := congrArg (fun z : Σ e : NonzeroCuts w, {t : Tag // t ∈ e.val.val} =>
    z.1.val.val) h
  have hi := congrArg (fun z : Σ e : NonzeroCuts w, {t : Tag // t ∈ e.val.val} =>
    z.2.val) h
  change ({p.val.1, p.val.2} : Finset Tag) = {q.val.1, q.val.2} at he
  change p.val.1 = q.val.1 at hi
  apply Subtype.ext
  rcases pair_eq he with h | h
  · exact Prod.ext h.1 h.2
  · exfalso
    exact q.property (congrArg w (hi.symm.trans h.1))

/--
---
conclusion: Lax342547.CutSparsity.unequal_card_le
---
An ordered unequal pair determines its nonzero cut and one of that cut's
two endpoints. This is an injection into the set of cut-endpoint flags.
-/
theorem unequal_card_le [Fintype Tag] (w : Tag → V) :
    Nat.card (UnequalPairs w) ≤ 2 * cutSize w := by
  classical
  let : Fintype (Component Tag) := inferInstanceAs (Fintype {e : Finset Tag // e.card = 2})
  let : Fintype (NonzeroCuts w) := inferInstanceAs (Fintype {e : Component Tag // cutMap w e ≠ 0})
  calc
    Nat.card (UnequalPairs w) ≤
        Nat.card (Σ e : NonzeroCuts w, {t : Tag // t ∈ e.val.val}) :=
      Nat.card_le_card_of_injective (pairFlag w) (pairFlag_injective w)
    _ = ∑ e : NonzeroCuts w, e.val.val.card := by
      rw [Nat.card_sigma]
      congr 1
      funext e
      simp [Nat.card_eq_fintype_card]
    _ = 2 * cutSize w := by
      simp [cutSize, fun e : NonzeroCuts w => e.val.property,
        Nat.card_eq_fintype_card, Nat.mul_comm]

omit [AddCommGroup V] [Module Binary V] in
theorem unequal_card_sum [Fintype Tag] (w : Tag → V) :
    Nat.card (UnequalPairs w) = ∑ i : Tag, Nat.card {j : Tag // w i ≠ w j} := by
  classical
  let e : UnequalPairs w ≃ Σ i : Tag, {j : Tag // w i ≠ w j} :=
    { toFun := fun p => ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
      invFun := fun z => ⟨(z.1, z.2.val), z.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]

omit [AddCommGroup V] [Module Binary V] in
theorem count_complement [Fintype Tag] (w : Tag → V) (c : V) :
    valueCount w c + Nat.card {t : Tag // w t ≠ c} = Fintype.card Tag := by
  classical
  simp only [valueCount, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le _)

/--
---
conclusion: Lax342547.CutSparsity.exists_majority
---
If every value class has size at most half the tags, each tag has at
least half the tags as unequal partners. Counting ordered pairs then
contradicts the assumed upper bound on nonzero unordered cuts.
-/
theorem exists_majority [Fintype Tag] (w : Tag → V)
    (h : 4 * cutSize w < Fintype.card Tag * Fintype.card Tag) :
    ∃ c : V, Fintype.card Tag < 2 * valueCount w c := by
  classical
  by_contra hn
  push Not at hn
  have hi (i : Tag) : Fintype.card Tag ≤ 2 * Nat.card {j : Tag // w i ≠ w j} := by
    have hc := count_complement w (w i)
    have hb := hn (w i)
    simpa only [ne_comm] using (show Fintype.card Tag ≤
      2 * Nat.card {j : Tag // w j ≠ w i} by omega)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Finset.mul_sum, ← unequal_card_sum] at hs
  have hu := Lax342547.CutSparsity.unequal_card_le w
  omega

theorem minority_product_le [Fintype Tag] (w : Tag → V) (c : V) :
    Nat.card {t : Tag // w t ≠ c} * valueCount w c ≤ cutSize w := by
  classical
  let : Fintype (Component Tag) := inferInstanceAs (Fintype {e : Finset Tag // e.card = 2})
  let : Fintype (NonzeroCuts w) := inferInstanceAs (Fintype {e : Component Tag // cutMap w e ≠ 0})
  let f : ({t : Tag // w t ≠ c} × {t : Tag // w t = c}) → NonzeroCuts w :=
    fun p => pairCut w ⟨(p.1.val, p.2.val), by simpa only [p.2.property] using p.1.property⟩
  have hf : Function.Injective f := by
    intro p q h
    have he := congrArg (fun e : NonzeroCuts w => e.val.val) h
    change ({p.1.val, p.2.val} : Finset Tag) = {q.1.val, q.2.val} at he
    rcases pair_eq he with h | h
    · exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · exact (p.1.property ((congrArg w h.1).trans q.2.property)).elim
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, valueCount, cutSize] using h

/--
---
conclusion: Lax342547.CutSparsity.minority_bound
---
Every minority-majority pair gives a distinct nonzero unordered cut.
The majority has more than half the tags, which yields the support bound.
-/
theorem minority_bound [Fintype Tag] (w : Tag → V) (c : V)
    (h : Fintype.card Tag < 2 * valueCount w c) :
    Fintype.card Tag * Nat.card {t : Tag // w t ≠ c} ≤ 2 * cutSize w := by
  have hp := minority_product_le w c
  have hm := Nat.mul_le_mul_right (Nat.card {t : Tag // w t ≠ c}) (Nat.le_of_lt h)
  nlinarith

omit [Module Binary V] in
theorem exists_common_zero [Fintype Tag] (w v : Tag → V)
    (hw : Fintype.card Tag < 2 * valueCount w 0)
    (hv : Fintype.card Tag < 2 * valueCount v 0) :
    ∃ t : Tag, w t = 0 ∧ v t = 0 := by
  classical
  let S := Finset.univ.filter (fun t => w t = 0)
  let T := Finset.univ.filter (fun t => v t = 0)
  have hs : S.card = valueCount w 0 := by simp [S, valueCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have ht : T.card = valueCount v 0 := by simp [T, valueCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  by_contra hn
  push Not at hn
  have hd : Disjoint S T := Finset.disjoint_left.mpr (by
    intro t hts htt
    exact hn t (Finset.mem_filter.mp hts).2 (Finset.mem_filter.mp htt).2)
  have hu := Finset.card_le_card (Finset.subset_univ (S ∪ T))
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ, hs, ht] at hu
  omega

/--
---
conclusion: Lax342547.CutSparsity.majority_unique
---
Equal cuts differ by a constant tuple. The two strict majority zero
sets intersect, so their common value forces that constant to be zero.
-/
theorem majority_unique [Fintype Tag] [Nonempty Tag] (w v : Tag → V)
    (hcut : cutMap w = cutMap v)
    (hw : Fintype.card Tag < 2 * valueCount w 0)
    (hv : Fintype.card Tag < 2 * valueCount v 0) : w = v := by
  obtain ⟨t, hwt, hvt⟩ := exists_common_zero w v hw hv
  obtain ⟨c, hc⟩ := (CutProfiles.cutMap_eq_iff w v).mp hcut
  have hzero : c = 0 := by simpa only [hwt, hvt, zero_add] using (hc t).symm
  funext i
  exact sub_eq_zero.mp (by simpa only [ZModModule.sub_eq_add, hzero] using hc i)

/--
---
conclusion: Lax342547.CutSparsity.exists_unique_normalized
---
The majority-intersection property puts the majority value in every
allowed tag space. Translating by it preserves the cut and all allowed
spaces, and the minority count becomes the support of the unique result.
-/
theorem exists_unique_normalized [Fintype Tag] [Nonempty Tag]
    (W : Tag → Submodule Binary V)
    (hW : ∀ S : Finset Tag, Fintype.card Tag < 2 * S.card →
      (⨅ t : {t // t ∈ S}, W t.val) ≤ ⨅ t, W t)
    (w : Tag → V) (hw : ∀ t, w t ∈ W t)
    (h : 4 * cutSize w < Fintype.card Tag * Fintype.card Tag) :
    ∃! v : Tag → V, (∀ t, v t ∈ W t) ∧ cutMap v = cutMap w ∧
      Fintype.card Tag < 2 * valueCount v 0 ∧
      Fintype.card Tag * supportSize v ≤ 2 * cutSize w := by
  classical
  obtain ⟨c, hc⟩ := Lax342547.CutSparsity.exists_majority w h
  let S := Finset.univ.filter (fun t => w t = c)
  have hs : S.card = valueCount w c := by
    simp [S, valueCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcW : c ∈ ⨅ t, W t := hW S (by rwa [hs]) (by
    simp only [Submodule.mem_iInf]
    intro t
    rw [← (Finset.mem_filter.mp t.property).2]
    exact hw t.val)
  let v : Tag → V := fun t => w t + c
  have hvc : ∀ t, v t = 0 ↔ w t = c := fun _ => by
    simp only [v, ← ZModModule.sub_eq_add, sub_eq_zero]
  have hvcount : valueCount v 0 = valueCount w c := by
    unfold valueCount
    exact Nat.card_congr (Equiv.subtypeEquivRight hvc)
  have hvsupport : supportSize v = Nat.card {t : Tag // w t ≠ c} := by
    unfold supportSize
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun t => not_congr (hvc t)))
  have hvcut : cutMap v = cutMap w := (CutProfiles.cutMap_eq_iff v w).2 ⟨c, fun t => by
    change w t + c + w t = c
    have hz : w t + w t = 0 := by rw [← ZModModule.sub_eq_add, sub_self]
    rw [add_right_comm, hz, zero_add]⟩
  refine ⟨v, ⟨?_, hvcut, ?_, ?_⟩, ?_⟩
  · intro t
    have hcWt : ∀ t, c ∈ W t := by simpa only [Submodule.mem_iInf] using hcW
    exact (W t).add_mem (hw t) (hcWt t)
  · rwa [hvcount]
  · rw [hvsupport]
    exact Lax342547.CutSparsity.minority_bound w c hc
  · intro u hu
    exact Lax342547.CutSparsity.majority_unique u v (hu.2.1.trans hvcut.symm) hu.2.2.1 (by rwa [hvcount])

end

end Lax342547Proofs.CutSparsity
