import Lax342547.SelectorInterpolation
import Lax342547Proofs.BaseMoments
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.SelectorInterpolation

open Lax342547.MomentSpace Lax342547.SelectorInterpolation

variable {b : ℕ}

theorem monomial_mem (S : Finset (Fin b)) {degree : ℕ} (h : S.card ≤ degree) :
    monomial S ∈ selectorSpan b degree := Submodule.subset_span ⟨S, h, rfl⟩

theorem span_mono {d e : ℕ} (h : d ≤ e) : selectorSpan b d ≤ selectorSpan b e := by
  apply Submodule.span_le.mpr
  rintro f ⟨S, hS, rfl⟩
  exact monomial_mem S (hS.trans h)

theorem mul_monomial_of_mem (S : Finset (Fin b)) {i : Fin b} (hi : i ∈ S)
    (s : Fin b → Binary) : s i * monomial S s = monomial S s := by
  unfold monomial
  rw [← Finset.mul_prod_erase S s hi, ← mul_assoc, BaseMoments.binary_mul_self]

theorem monomial_insert (S : Finset (Fin b)) (i : Fin b) (s : Fin b → Binary) :
    monomial (insert i S) s = s i * monomial S s := by
  by_cases hi : i ∈ S
  · rw [Finset.insert_eq_of_mem hi]
    exact (mul_monomial_of_mem S hi s).symm
  · simp [monomial, hi]

theorem monomial_mul (S T : Finset (Fin b)) : monomial S * monomial T = monomial (S ∪ T) := by
  ext s
  change monomial S s * monomial T s = monomial (S ∪ T) s
  induction S using Finset.induction_on with
  | empty => simp [monomial]
  | @insert i S hi ih => rw [Finset.insert_union, monomial_insert, monomial_insert, ← ih, mul_assoc]

theorem mul_mem {d e : ℕ} {f g : (Fin b → Binary) → Binary}
    (hf : f ∈ selectorSpan b d) (hg : g ∈ selectorSpan b e) :
    f * g ∈ selectorSpan b (d + e) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S, hS, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨T, hT, rfl⟩ := hg
      rw [monomial_mul]
      exact monomial_mem _ ((Finset.card_union_le _ _).trans (Nat.add_le_add hS hT))
    | zero => simp
    | add g h _ _ hg hh => simpa [mul_add] using (selectorSpan b (d + e)).add_mem hg hh
    | smul c g _ hg => simpa [mul_smul_comm] using (selectorSpan b (d + e)).smul_mem c hg
  | zero => simp
  | add f h _ _ hf hh => simpa [add_mul] using (selectorSpan b (d + e)).add_mem hf hh
  | smul c f _ hf => simpa [smul_mul_assoc] using (selectorSpan b (d + e)).smul_mem c hf

theorem constant_mem (c : Binary) (degree : ℕ) : (fun _ : Fin b → Binary => c) ∈ selectorSpan b degree := by
  have h := (selectorSpan b degree).smul_mem c (monomial_mem ∅ (Nat.zero_le degree))
  have he : c • monomial (∅ : Finset (Fin b)) = fun _ => c := by
    ext s
    simp [monomial]
  rw [he] at h
  exact h

theorem affine_mem (i : Fin b) (c : Binary) : (fun s : Fin b → Binary => s i + c) ∈ selectorSpan b 1 := by
  have h := (selectorSpan b 1).add_mem (monomial_mem {i} (by simp)) (constant_mem c 1)
  have he : monomial {i} + (fun _ : Fin b → Binary => c) = fun s => s i + c := by
    ext s
    simp [monomial]
  rw [he] at h
  exact h

theorem prod_mem {ι : Type} (S : Finset ι) (f : ι → (Fin b → Binary) → Binary)
    (hf : ∀ i ∈ S, f i ∈ selectorSpan b 1) : (∏ i ∈ S, f i) ∈ selectorSpan b S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.card_empty]
    exact constant_mem 1 0
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_comm]
    exact mul_mem (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem affine_self (x : Binary) : x + (1 + x) = 1 := by
  rw [add_left_comm, ZModModule.add_self, add_zero]

theorem affine_other (x y : Binary) (h : x ≠ y) : x + (1 + y) = 0 := by
  fin_cases x <;> fin_cases y <;> first | rfl | exact False.elim (h rfl)

theorem exists_separator {ι : Type} [Fintype ι] [DecidableEq ι] {degree : ℕ}
    (s : ι → Fin b → Binary) (hs : Function.Injective s)
    (hdegree : Fintype.card ι ≤ degree + 1) (i₀ : ι) :
    ∃ f ∈ selectorSpan b degree, ∀ i, f (s i) = if i = i₀ then 1 else 0 := by
  classical
  let Others := {j : ι // j ≠ i₀}
  have differs (j : Others) : ∃ a, s j.val a ≠ s i₀ a :=
    Function.ne_iff.mp (fun h => j.property (hs h))
  choose a ha using differs
  let factors : Others → (Fin b → Binary) → Binary :=
    fun j x => x (a j) + (1 + s i₀ (a j))
  let f : (Fin b → Binary) → Binary := ∏ j, factors j
  have hcard : Fintype.card Others ≤ degree := by
    have hc : Fintype.card Others = Fintype.card ι - 1 := by
      simp [Others, Fintype.card_subtype_compl]
    omega
  refine ⟨f, span_mono hcard (prod_mem Finset.univ factors (fun j _ => affine_mem _ _)), ?_⟩
  intro i
  dsimp only [f]
  rw [Finset.prod_apply]
  by_cases hi : i = i₀
  · subst i
    rw [if_pos rfl]
    exact Finset.prod_eq_one (fun j _ => affine_self _)
  · rw [if_neg hi]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨i, hi⟩ : Others)) (affine_other _ _ (ha ⟨i, hi⟩))

set_option backward.isDefEq.respectTransparency false in
theorem sum_eval_eq_zero {ι : Type} [Fintype ι] {degree : ℕ}
    (s : ι → Fin b → Binary) (c : ι → Binary)
    (h : ∑ i, c i • selectorEval (degree := degree) (s i) = 0)
    {f : (Fin b → Binary) → Binary} (hf : f ∈ selectorSpan b degree) :
    ∑ i, c i * f (s i) = 0 := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨S, hS, rfl⟩ := hf
    have he := congrFun h (⟨S, hS⟩ : SelectorCoordinates b degree)
    rw [Finset.sum_apply] at he
    simpa only [Pi.smul_apply, smul_eq_mul, selectorEval, monomial, Pi.zero_apply] using he
  | zero => simp
  | add f g _ _ hf hg => simpa [mul_add, Finset.sum_add_distrib] using congrArg₂ (· + ·) hf hg
  | smul a f _ hf =>
    simpa [mul_left_comm, ← Finset.mul_sum] using congrArg (a * ·) hf

/--
---
conclusion: Lax342547.SelectorInterpolation.selectorEval_linearIndependent
---
For each label, a product of affine bit functions singles it out among the
specified labels. Its degree is at most their number minus one. Applying
these separating polynomials to a linear relation recovers every coefficient.
-/
theorem selectorEval_linearIndependent {ι : Type} [Fintype ι] {b degree : ℕ}
    (s : ι → Fin b → Binary) (hs : Function.Injective s)
    (hdegree : Fintype.card ι ≤ degree + 1) :
    LinearIndependent Binary (fun i => selectorEval (degree := degree) (s i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i₀
  obtain ⟨f, hf, he⟩ := exists_separator s hs hdegree i₀
  have h := sum_eval_eq_zero s c hc hf
  simpa [he] using h

end Lax342547Proofs.SelectorInterpolation
