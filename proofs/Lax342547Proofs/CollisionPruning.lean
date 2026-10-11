import Lax342547.CollisionPruning

namespace Lax342547Proofs.CollisionPruning
open Lax342547.CollisionPruning

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.CollisionPruning.retained_nonneg
---
-/
theorem retained_nonneg {C : Type} [Fintype C] (a : C → ℝ) (τ : ℝ) (ha : ∀ c, 0 ≤ a c) :
    0 ≤ retained a τ := by
  classical
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact ha c
  · exact le_rfl

/--
---
conclusion: Lax342547.CollisionPruning.retained_le
---
-/
theorem retained_le {C : Type} [Fintype C] (a : C → ℝ) (τ : ℝ) (ha : ∀ c, 0 ≤ a c) :
    retained a τ ≤ ∑ c, a c := by
  classical
  apply Finset.sum_le_sum
  intro c _
  split_ifs
  · exact le_rfl
  · exact ha c

/--
---
conclusion: Lax342547.CollisionPruning.retained_loss
---
-/
theorem retained_loss {C : Type} [Fintype C] (a : C → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ c, a c) - retained a τ ≤ Fintype.card C * τ := by
  classical
  have he : (∑ c, a c) - retained a τ = ∑ c, (a c - if τ ≤ a c then a c else 0) := by
    rw [Finset.sum_sub_distrib]
    rfl
  rw [he]
  have h : (∑ c, (a c - if τ ≤ a c then a c else 0)) ≤ ∑ _ : C, τ := by
    apply Finset.sum_le_sum
    intro c _
    split_ifs with hc
    · simpa using hτ
    · simpa using (not_le.mp hc).le
  simpa using h

/--
---
conclusion: Lax342547.CollisionPruning.paired_pruning
---
-/
theorem paired_pruning {Q C D : Type} [Fintype Q] [Fintype C] [Fintype D]
    (a : Q → C → ℝ) (b : Q → D → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (ha : ∀ q c, 0 ≤ a q c) (hb : ∀ q d, 0 ≤ b q d)
    (hasum : (∑ q, ∑ c, a q c) ≤ 1) (hbsum : (∑ q, ∑ d, b q d) ≤ 1) :
    (∑ q, (∑ c, a q c) * (∑ d, b q d)) -
      (∑ q, retained (a q) τ * retained (b q) τ) ≤
        (Fintype.card C + Fintype.card D : ℝ) * τ := by
  classical
  have hpoint (q : Q) : (∑ c, a q c) * (∑ d, b q d) - retained (a q) τ * retained (b q) τ ≤
      (Fintype.card C : ℝ) * τ * (∑ d, b q d) + (Fintype.card D : ℝ) * τ * (∑ c, a q c) := by
    have hA := Lax342547.CollisionPruning.retained_nonneg (a q) τ (ha q)
    have hB := Lax342547.CollisionPruning.retained_nonneg (b q) τ (hb q)
    have hA' := Lax342547.CollisionPruning.retained_le (a q) τ (ha q)
    have hB' := Lax342547.CollisionPruning.retained_le (b q) τ (hb q)
    have hlossA := Lax342547.CollisionPruning.retained_loss (a q) τ hτ
    have hlossB := Lax342547.CollisionPruning.retained_loss (b q) τ hτ
    have htotB : 0 ≤ ∑ d, b q d := Finset.sum_nonneg (fun d _ => hb q d)
    have hcD : 0 ≤ (Fintype.card D : ℝ) * τ := mul_nonneg (Nat.cast_nonneg _) hτ
    have hmulA := mul_le_mul_of_nonneg_right hlossA htotB
    have hmulB := mul_le_mul_of_nonneg_left hlossB hA
    have hmulC := mul_le_mul_of_nonneg_left hA' hcD
    nlinarith
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q, ((Fintype.card C : ℝ) * τ * (∑ d, b q d) +
        (Fintype.card D : ℝ) * τ * (∑ c, a q c)) := Finset.sum_le_sum (fun q _ => hpoint q)
    _ = (Fintype.card C : ℝ) * τ * (∑ q, ∑ d, b q d) +
        (Fintype.card D : ℝ) * τ * (∑ q, ∑ c, a q c) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by
      have hA := mul_le_mul_of_nonneg_left hbsum (mul_nonneg (Nat.cast_nonneg (Fintype.card C)) hτ)
      have hB := mul_le_mul_of_nonneg_left hasum (mul_nonneg (Nat.cast_nonneg (Fintype.card D)) hτ)
      nlinarith


/--
---
conclusion: Lax342547.CollisionPruning.averaged_pruning
---
-/
theorem averaged_pruning {A B Q C D : Type} [Fintype A] [Fintype B]
    [Fintype Q] [Fintype C] [Fintype D]
    (pA : A → ℝ) (pB : B → ℝ)
    (a : A → B → Q → C → ℝ) (b : B → A → Q → D → ℝ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hpA : ∀ x, 0 ≤ pA x) (hpB : ∀ y, 0 ≤ pB y)
    (hsA : ∑ x, pA x = 1) (hsB : ∑ y, pB y = 1)
    (ha : ∀ x y q c, 0 ≤ a x y q c) (hb : ∀ y x q d, 0 ≤ b y x q d)
    (haSum : ∀ x y, (∑ q, ∑ c, a x y q c) ≤ 1)
    (hbSum : ∀ y x, (∑ q, ∑ d, b y x q d) ≤ 1) :
    (∑ x, ∑ y, pA x * pB y *
      ((∑ q, (∑ c, a x y q c) * (∑ d, b y x q d)) -
        (∑ q, retained (a x y q) τ * retained (b y x q) τ))) ≤
      (Fintype.card C + Fintype.card D : ℝ) * τ := by
  have hpair (x : A) (y : B) := Lax342547.CollisionPruning.paired_pruning (a x y) (b y x) τ hτ
    (ha x y) (hb y x) (haSum x y) (hbSum y x)
  calc
    _ ≤ ∑ x, ∑ y, pA x * pB y * ((Fintype.card C + Fintype.card D : ℝ) * τ) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hpair x y) (mul_nonneg (hpA x) (hpB y))
    _ = _ := by
      simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hsA, hsB, one_mul]

end Lax342547Proofs.CollisionPruning
