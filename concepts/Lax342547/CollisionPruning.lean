import Lax342547.PrimalRecords
import Lax342547.Walsh

/-!
---
title: Pruning small unary record cells
type: definition and theorem
---
The collision loss is bounded by the two cell counts times the threshold. Independent parameter averaging permits dependence of each record partition on opposite parameters.
-/

namespace Lax342547.CollisionPruning



noncomputable def retained {C : Type} [Fintype C] (a : C → ℝ) (τ : ℝ) : ℝ :=
  ∑ c, if τ ≤ a c then a c else 0

axiom retained_nonneg {C : Type} [Fintype C] (a : C → ℝ) (τ : ℝ) (ha : ∀ c, 0 ≤ a c) :
    0 ≤ retained a τ

axiom retained_le {C : Type} [Fintype C] (a : C → ℝ) (τ : ℝ) (ha : ∀ c, 0 ≤ a c) :
    retained a τ ≤ ∑ c, a c

axiom retained_loss {C : Type} [Fintype C] (a : C → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (∑ c, a c) - retained a τ ≤ Fintype.card C * τ

axiom paired_pruning {Q C D : Type} [Fintype Q] [Fintype C] [Fintype D]
    (a : Q → C → ℝ) (b : Q → D → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (ha : ∀ q c, 0 ≤ a q c) (hb : ∀ q d, 0 ≤ b q d)
    (hasum : (∑ q, ∑ c, a q c) ≤ 1) (hbsum : (∑ q, ∑ d, b q d) ≤ 1) :
    (∑ q, (∑ c, a q c) * (∑ d, b q d)) -
      (∑ q, retained (a q) τ * retained (b q) τ) ≤
        (Fintype.card C + Fintype.card D : ℝ) * τ

axiom averaged_pruning {A B Q C D : Type} [Fintype A] [Fintype B]
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
      (Fintype.card C + Fintype.card D : ℝ) * τ

end Lax342547.CollisionPruning
