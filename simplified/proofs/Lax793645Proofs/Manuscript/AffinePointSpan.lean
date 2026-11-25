import Lax793645.AffinePointMatrices

namespace Lax793645Proofs.Manuscript.AffinePointMatrices
open Lax793645.AffinePointMatrices

private abbrev Mat (I : Type) := Matrix (Option I) (Option I) (ZMod 2)
private abbrev spanPoints (I : Type) := Submodule.span (ZMod 2) (Set.range (@pointSquare I))

private theorem generator {I : Type} (z : I → ZMod 2) : pointSquare z ∈ spanPoints I :=
  Submodule.subset_span ⟨z, rfl⟩

private theorem identities {I : Type} (M : Mat I) (h : M ∈ spanPoints I) :
    (∀ i j, M i j = M j i) ∧ ∀ i, M (some i) (some i) = M (some i) none := by
  induction h using Submodule.span_induction with
  | mem M h =>
    obtain ⟨z, rfl⟩ := h
    constructor
    · intro i j
      apply mul_comm
    · intro i
      change z i * z i = z i * 1
      rw [mul_one]
      exact (by decide : ∀ t : ZMod 2, t * t = t) (z i)
  | zero => exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | add x y _ _ hx hy =>
    constructor
    · intro i j
      simp only [Matrix.add_apply, hx.1 i j, hy.1 i j]
    · intro i
      simp only [Matrix.add_apply, hx.2, hy.2]
  | smul c x _ hx =>
    constructor
    · intro i j
      simp only [Matrix.smul_apply, hx.1 i j]
    · intro i
      simp only [Matrix.smul_apply, hx.2]

/--
---
conclusion: Lax793645.AffinePointMatrices.mem_span_pointSquare_iff
---
Eliminate an ordinary row and its column together. Two affine point
squares suffice to match every entry in that row, including its diagonal.
When only the constant entry remains, the point at zero supplies it.
-/
theorem mem_span_pointSquare_iff {I : Type} [Fintype I] (M : Mat I) :
    M ∈ spanPoints I ↔
      (∀ i j, M i j = M j i) ∧ ∀ i, M (some i) (some i) = M (some i) none := by
  classical
  refine ⟨identities M, ?_⟩
  have eliminate (S : Finset I) : ∀ A : Mat I,
      (∀ i j, A i j = A j i) → (∀ i, A (some i) (some i) = A (some i) none) →
      (∀ k ∉ S, ∀ j, A (some k) j = 0) → A ∈ spanPoints I := by
    induction S using Finset.induction_on with
    | empty =>
      intro A hs hd hz
      have he : A = A none none • pointSquare (0 : I → ZMod 2) := by
        ext i j
        cases i <;> cases j <;> simp [pointSquare, Matrix.vecMulVec, Option.elim', hs none, hz]
      exact he ▸ (spanPoints I).smul_mem _ (generator _)
    | @insert i S hi ih =>
      intro A hs hd hz
      let z (k : I) : ZMod 2 := if k = i then 1 else A (some k) (some i)
      let e (k : I) : ZMod 2 := if k = i then 1 else 0
      let C := pointSquare z + (A (some i) (some i) - 1) • pointSquare e
      have hc : C ∈ spanPoints I := (spanPoints I).add_mem (generator _) ((spanPoints I).smul_mem _ (generator _))
      obtain ⟨cs, cd⟩ := identities C hc
      have row (j : Option I) : C (some i) j = A (some i) j := by
        cases j with
        | none =>
          simp [C, pointSquare, Matrix.vecMulVec, Option.elim', z, e, ←hd i]
        | some k =>
          by_cases hk : k = i
          · subst k
            simp [C, pointSquare, Matrix.vecMulVec, Option.elim', z, e]
          · simp [C, pointSquare, Matrix.vecMulVec, Option.elim', z, e, hk, hs (some k) (some i)]
      have remaining : A - C ∈ spanPoints I := by
        apply ih
        · intro j k
          simp only [Matrix.sub_apply, hs j k, cs j k]
        · intro k
          simp only [Matrix.sub_apply, hd, cd]
        · intro k hk j
          by_cases hki : k = i
          · subst k
            simp only [Matrix.sub_apply, row, sub_self]
          · have outside : k ∉ insert i S := by simp [hki, hk]
            simp [Matrix.sub_apply, hz k outside, C, pointSquare, Matrix.vecMulVec,
              Option.elim', z, e, hki]
      simpa only [sub_add_cancel] using (spanPoints I).add_mem remaining hc
  rintro ⟨hs, hd⟩
  exact eliminate Finset.univ M hs hd (by simp)

end Lax793645Proofs.Manuscript.AffinePointMatrices
