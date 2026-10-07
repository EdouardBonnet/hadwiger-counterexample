import Lax342547.JointProjectors
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

namespace Lax342547Proofs.JointProjectors

open Lax342547.MomentSpace

section CommutativeRing

variable {A ι : Type} [CommRing A] [Fintype ι]

def bitFactor (e : A) (s : Binary) : A := if s = 0 then 1 - e else e

def projector (e : ι → A) (s : ι → Binary) : A := ∏ i, bitFactor (e i) (s i)

theorem bitFactor_square (e : A) (he : e * e = e) (s : Binary) :
    bitFactor e s * bitFactor e s = bitFactor e s := by
  by_cases hs : s = 0
  · simp only [bitFactor, if_pos hs]
    calc (1 - e) * (1 - e) = 1 - e - e + e * e := by ring
         _ = 1 - e := by rw [he]; ring
  · simpa only [bitFactor, if_neg hs] using he

theorem bitFactor_mul_ne (e : A) (he : e * e = e) (s t : Binary) (hst : s ≠ t) :
    bitFactor e s * bitFactor e t = 0 := by
  fin_cases s <;> fin_cases t
  · exact False.elim (hst rfl)
  · simp [bitFactor, sub_mul, he]
  · simp [bitFactor, mul_sub, he]
  · exact False.elim (hst rfl)

theorem projector_square (e : ι → A) (he : ∀ i, e i * e i = e i) (s : ι → Binary) :
    projector e s * projector e s = projector e s := by
  unfold projector
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => bitFactor_square _ (he i) _)

theorem projector_mul_ne (e : ι → A) (he : ∀ i, e i * e i = e i)
    (s t : ι → Binary) (hst : s ≠ t) : projector e s * projector e t = 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hst
  unfold projector
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (bitFactor_mul_ne _ (he i) _ _ hi)

theorem bitFactor_sum (e : A) : ∑ s : Binary, bitFactor e s = 1 := by
  change (∑ s : Fin 2, bitFactor e s) = 1
  rw [Fin.sum_univ_two]
  simp [bitFactor]

theorem projector_sum [DecidableEq ι] (e : ι → A) : ∑ s : ι → Binary, projector e s = 1 := by
  classical
  have h := Fintype.prod_sum (fun (i : ι) (s : Binary) => bitFactor (e i) s)
  simpa only [bitFactor_sum, Finset.prod_const_one, projector] using h.symm

theorem mul_projector (e : ι → A) (he : ∀ i, e i * e i = e i)
    (s : ι → Binary) (i : ι) :
    e i * projector e s = if s i = 0 then 0 else projector e s := by
  classical
  unfold projector
  rw [← Finset.mul_prod_erase Finset.univ (fun j => bitFactor (e j) (s j)) (Finset.mem_univ i)]
  by_cases hs : s i = 0
  · simp [bitFactor, hs, ← mul_assoc, mul_sub, he]
  · simp [bitFactor, hs, ← mul_assoc, he]

end CommutativeRing

section Endomorphisms

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module Binary V]

theorem bit_smul (c : Binary) (x : V) : c • x = if c = 0 then 0 else x := by
  fin_cases c <;> simp

open scoped IsMulCommutative in
theorem exists_joint_projectors (M : ι → Module.End Binary V)
    (hid : ∀ i, M i * M i = M i) (hcomm : ∀ i j, M i * M j = M j * M i) :
    ∃ P : (ι → Binary) → Module.End Binary V,
      (∑ s, P s) = 1 ∧ (∀ s, P s * P s = P s) ∧
      (∀ s t, s ≠ t → P s * P t = 0) ∧ ∀ i s, M i * P s = s i • P s := by
  let C := Algebra.adjoin Binary (Set.range M)
  have hC : IsMulCommutative C := Algebra.isMulCommutative_adjoin Binary (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hcomm i j)
  let e (i : ι) : C := ⟨M i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have he (i : ι) : e i * e i = e i := Subtype.ext (hid i)
  let P (s : ι → Binary) : Module.End Binary V := (projector e s : C)
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun x : C => (x : Module.End Binary V)) (projector_sum e)
    simpa [P] using h
  · intro s
    exact congrArg (fun x : C => (x : Module.End Binary V)) (projector_square e he s)
  · intro s t hst
    exact congrArg (fun x : C => (x : Module.End Binary V)) (projector_mul_ne e he s t hst)
  · intro i s
    have h := congrArg (fun x : C => (x : Module.End Binary V)) (mul_projector e he s i)
    rw [bit_smul]
    simpa only [P, e, Subalgebra.coe_mul, Subalgebra.coe_mk, apply_ite, Subalgebra.coe_zero] using h

end Endomorphisms

section ProjectionFamily

variable {K L V : Type} [Field K] [Fintype L] [DecidableEq L]
  [AddCommGroup V] [Module K V]

omit [Fintype L] in
theorem apply_of_mem_range (P : L → Module.End K V)
    (hid : ∀ s, P s * P s = P s) (horth : ∀ s t, s ≠ t → P s * P t = 0)
    (s t : L) (x : V) (hx : x ∈ LinearMap.range (P t)) :
    P s x = if s = t then x else 0 := by
  obtain ⟨y, rfl⟩ := hx
  by_cases hst : s = t
  · subst t
    rw [if_pos rfl]
    exact LinearMap.congr_fun (hid s) y
  · rw [if_neg hst]
    exact LinearMap.congr_fun (horth s t hst) y

theorem exists_decomposition (P : L → Module.End K V) (hsum : ∑ s, P s = 1)
    (hid : ∀ s, P s * P s = P s) (horth : ∀ s t, s ≠ t → P s * P t = 0) :
    ∃ E : V ≃ₗ[K] (∀ s, LinearMap.range (P s)),
      ∀ x s, (E x s : V) = P s x := by
  let F : V →ₗ[K] (∀ s, LinearMap.range (P s)) :=
    LinearMap.pi (fun s => (P s).rangeRestrict)
  have hsum_apply (x : V) : ∑ s, P s x = x := by
    simpa using LinearMap.congr_fun hsum x
  have hinj : Function.Injective F := by
    intro x y hxy
    have he (s : L) : P s x = P s y := congrArg Subtype.val (congrFun hxy s)
    rw [← hsum_apply x, ← hsum_apply y]
    exact Finset.sum_congr rfl (fun s _ => he s)
  have hsurj : Function.Surjective F := by
    intro x
    refine ⟨∑ t, (x t : V), ?_⟩
    funext s
    apply Subtype.ext
    change P s (∑ t, (x t : V)) = (x s : V)
    rw [map_sum]
    simp_rw [apply_of_mem_range P hid horth s _ _ (x _).property]
    simp
  exact ⟨LinearEquiv.ofBijective F ⟨hinj, hsurj⟩, fun _ _ => rfl⟩

theorem sum_range_finrank [FiniteDimensional K V]
    (P : L → Module.End K V) (hsum : ∑ s, P s = 1)
    (hid : ∀ s, P s * P s = P s) (horth : ∀ s t, s ≠ t → P s * P t = 0) :
    ∑ s, Module.finrank K (LinearMap.range (P s)) = Module.finrank K V := by
  obtain ⟨E, _⟩ := exists_decomposition P hsum hid horth
  simpa only [Module.finrank_pi_fintype] using E.finrank_eq.symm

omit [Fintype L] in
theorem range_independent (P : L → Module.End K V)
    (hid : ∀ s, P s * P s = P s) (horth : ∀ s t, s ≠ t → P s * P t = 0) :
    iSupIndep (fun s => LinearMap.range (P s)) := by
  intro s
  have hle : (⨆ (t) (_ : t ≠ s), LinearMap.range (P t)) ≤ (P s).ker := by
    refine iSup_le (fun t => iSup_le (fun hts => ?_))
    intro x hx
    change P s x = 0
    simpa [Ne.symm hts] using apply_of_mem_range P hid horth s t x hx
  apply Disjoint.mono_right hle
  rw [disjoint_iff, Submodule.eq_bot_iff]
  intro x hx
  have hfix : P s x = x := by simpa using apply_of_mem_range P hid horth s s x hx.1
  exact hfix.symm.trans hx.2

theorem nonzero_projector_count [FiniteDimensional K V]
    (P : L → Module.End K V)
    (hid : ∀ s, P s * P s = P s) (horth : ∀ s t, s ≠ t → P s * P t = 0) :
    Nat.card {s // P s ≠ 0} ≤ Module.finrank K V := by
  classical
  have h := (range_independent P hid horth).subtype_ne_bot_le_finrank
  have he (s : L) : LinearMap.range (P s) ≠ ⊥ ↔ P s ≠ 0 := by
    constructor
    · intro hn hz; apply hn; rw [hz, LinearMap.range_zero]
    · intro hn hz; apply hn
      apply LinearMap.ext
      intro x
      have hx : P s x ∈ (⊥ : Submodule K V) := hz ▸ LinearMap.mem_range_self (P s) x
      exact hx
  have hc := Fintype.card_congr (Equiv.subtypeEquivRight he)
  rw [hc] at h
  simpa only [Nat.card_eq_fintype_card] using h

end ProjectionFamily

section Orthogonality

variable {ι V : Type} [AddCommGroup V] [Module Binary V]

theorem different_labels_orthogonal (B : LinearMap.BilinForm Binary V)
    (M : ι → Module.End Binary V)
    (hadj : ∀ i x y, B (M i x) y = B x (M i y))
    (P : (ι → Binary) → Module.End Binary V)
    (heigen : ∀ i s, M i * P s = s i • P s)
    (s t : ι → Binary) (hst : s ≠ t) (x y : V) : B (P s x) (P t y) = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hst
  have hsx : M i (P s x) = s i • P s x := LinearMap.congr_fun (heigen i s) x
  have hty : M i (P t y) = t i • P t y := LinearMap.congr_fun (heigen i t) y
  by_contra hne
  apply hi
  apply mul_right_cancel₀ hne
  calc
    s i * B (P s x) (P t y) = B (s i • P s x) (P t y) := by simp
    _ = B (M i (P s x)) (P t y) := by rw [hsx]
    _ = B (P s x) (M i (P t y)) := hadj i _ _
    _ = B (P s x) (t i • P t y) := by rw [hty]
    _ = t i * B (P s x) (P t y) := by simp

end Orthogonality

theorem pairing_decomposition {K L V : Type} [Field K] [Fintype L] [DecidableEq L]
    [AddCommGroup V] [Module K V] (B : LinearMap.BilinForm K V)
    (P : L → Module.End K V) (hsum : ∑ s, P s = 1)
    (horth : ∀ s t, s ≠ t → ∀ x y, B (P s x) (P t y) = 0) (x y : V) :
    B x y = ∑ s, B (P s x) (P s y) := by
  have hx : x = ∑ s, P s x := by simpa using (LinearMap.congr_fun hsum x).symm
  have hy : y = ∑ s, P s y := by simpa using (LinearMap.congr_fun hsum y).symm
  calc
    B x y = B (∑ s, P s x) (∑ t, P t y) := congrArg₂ (fun u v => B u v) hx hy
    _ = ∑ s, ∑ t, B (P s x) (P t y) := by simp; exact Finset.sum_comm
    _ = ∑ s, B (P s x) (P s y) := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_eq_single s (fun t _ hts => horth s t (Ne.symm hts) x y) (by simp)

theorem right_eigen {ι V : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module Binary V]
    (M : ι → Module.End Binary V) (P : (ι → Binary) → Module.End Binary V)
    (hsum : ∑ s, P s = 1) (hid : ∀ s, P s * P s = P s)
    (horth : ∀ s t, s ≠ t → P s * P t = 0)
    (heigen : ∀ i s, M i * P s = s i • P s) (i : ι) (s : ι → Binary) :
    P s * M i = s i • P s := by
  classical
  apply LinearMap.ext
  intro x
  have hx : x = ∑ t, P t x := by simpa using (LinearMap.congr_fun hsum x).symm
  have hev (t : ι → Binary) : M i (P t x) = t i • P t x :=
    LinearMap.congr_fun (heigen i t) x
  change P s (M i x) = s i • P s x
  calc
    _ = P s (M i (∑ t, P t x)) := congrArg (fun z => P s (M i z)) hx
    _ = ∑ t, t i • P s (P t x) := by simp [hev]
    _ = s i • P s x := by
      rw [Finset.sum_eq_single s]
      · exact congrArg (s i • ·) (LinearMap.congr_fun (hid s) x)
      · intro t _ hts
        have hz : P s (P t x) = 0 := LinearMap.congr_fun (horth s t (Ne.symm hts)) x
        rw [hz, smul_zero]
      · simp

/--
---
conclusion: Lax342547.JointProjectors.exists_joint_decomposition
---
Work in the commutative algebra generated by the operators. Products of
the selected operators and their complements give mutually annihilating
idempotents whose sum is the identity. Their ranges give a linear
decomposition, so their dimensions add and bound the number of nonzero labels.
-/
theorem exists_joint_decomposition {ι V : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module Binary V] [FiniteDimensional Binary V]
    (M : ι → Module.End Binary V)
    (hid : ∀ i, M i * M i = M i) (hcomm : ∀ i j, M i * M j = M j * M i) :
    ∃ P : (ι → Binary) → Module.End Binary V,
      (∑ s, P s) = 1 ∧ (∀ s, P s * P s = P s) ∧
      (∀ s t, s ≠ t → P s * P t = 0) ∧
      (∀ i s, M i * P s = s i • P s) ∧
      (∑ s, Module.finrank Binary (LinearMap.range (P s))) = Module.finrank Binary V ∧
      Nat.card {s // P s ≠ 0} ≤ Module.finrank Binary V := by
  obtain ⟨P, hsum, hidP, horth, heigen⟩ := exists_joint_projectors M hid hcomm
  exact ⟨P, hsum, hidP, horth, heigen, sum_range_finrank P hsum hidP horth,
    nonzero_projector_count P hidP horth⟩

end Lax342547Proofs.JointProjectors
