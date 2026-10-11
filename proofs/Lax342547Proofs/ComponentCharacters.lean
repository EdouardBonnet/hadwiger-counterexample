import Lax342547.ComponentCharacters
import Lax342547.CoefficientPhase
import Lax342547.GramTests
import Lax342547.ProjectedCoefficients
import Lax342547.QuotientFactors
import Lax342547.RetainedCharacters
import Lax342547Proofs.Walsh

namespace Lax342547Proofs.ComponentCharacters
open Lax342547.ComponentCharacters

set_option backward.isDefEq.respectTransparency false
open Lax342547.ConcreteGeometry
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.CoefficientPhase
open Lax342547.PushforwardWalsh Lax342547.RetainedCharacters

/--
---
conclusion: Lax342547.ComponentCharacters.block_factor_pair
---
-/
theorem block_factor_pair {Axis N : Type} {I R : Axis → Type}
    [Fintype Axis] [Fintype N] [∀ a, Fintype (I a)] [∀ a, Fintype (R a)]
    (A B : ∀ a, Matrix (I a) (R a) Binary) (X Y : ∀ a, Matrix N (I a) Binary) :
    (∑ a, coefficientPair (A a * (B a).transpose) (X a) (Y a)) =
      dotProduct (blockImage A X) (blockImage B Y) := by
  classical
  simp only [Lax342547.CoefficientPhase.independent_factor_phase]
  unfold dotProduct blockImage
  simp only [Fintype.sum_prod_type, Fintype.sum_sigma]

/--
---
conclusion: Lax342547.ComponentCharacters.block_factor_phase
---
-/
theorem block_factor_phase {Axis N : Type} {I R : Axis → Type}
    [Fintype Axis] [Fintype N] [∀ a, Fintype (I a)] [∀ a, Fintype (R a)]
    (A B : ∀ a, Matrix (I a) (R a) Binary) (X Y : ∀ a, Matrix N (I a) Binary) :
    sign (∑ a, coefficientPair (A a * (B a).transpose) (X a) (Y a)) =
      phase (blockImage A X) (blockImage B Y) := by
  rw [Lax342547.ComponentCharacters.block_factor_pair]
  rfl

/--
---
conclusion: Lax342547.ComponentCharacters.block_image_dimension
---
-/
theorem block_image_dimension {Axis N : Type} {R : Axis → Type}
    [Fintype Axis] [Fintype N] [∀ a, Fintype (R a)] :
    Fintype.card ((Σ a, R a) × N) = (∑ a, Fintype.card (R a)) * Fintype.card N := by
  rw [Fintype.card_prod, Fintype.card_sigma]

/--
---
conclusion: Lax342547.ComponentCharacters.component_character_bound
---
-/
theorem component_character_bound {ΩA ΩB Axis N : Type} {I R : Axis → Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype Axis] [Fintype N]
    [∀ a, Fintype (I a)] [∀ a, Fintype (R a)]
    (α : ΩA → ℝ) (β : ΩB → ℝ)
    (X : ΩA → ∀ a, Matrix N (I a) Binary) (Y : ΩB → ∀ a, Matrix N (I a) Binary)
    (A B : ∀ a, Matrix (I a) (R a) Binary) (c : Binary)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    (hαsum : ∑ x, α x ≤ 1) (hβsum : ∑ y, β y ≤ 1)
    (hcapA : ∀ x, push α (fun ω => blockImage A (X ω)) x ≤
      (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, Fintype.card (R a))*Fintype.card N)))
    (hcapB : ∀ y, push β (fun ω => blockImage B (Y ω)) y ≤
      (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, Fintype.card (R a))*Fintype.card N))) :
    |∑ x, ∑ y, α x * β y * sign ((∑ a,
      coefficientPair (A a * (B a).transpose) (X x a) (Y y a)) + c)| ≤
      (2 : ℝ)^(-(45/100 : ℝ)*((∑ a, Fintype.card (R a))*Fintype.card N)) := by
  classical
  have h := Lax342547.GramTests.paper_image_walsh α β
    (fun ω => blockImage A (X ω)) (fun ω => blockImage B (Y ω))
    (fun _ => sign c) (fun _ => 1) hα hβ hαsum hβsum
    (by simpa only [Lax342547.ComponentCharacters.block_image_dimension, Nat.cast_mul] using hcapA)
    (by simpa only [Lax342547.ComponentCharacters.block_image_dimension, Nat.cast_mul] using hcapB)
    (fun _ => (Lax342547.RetainedCharacters.sign_abs c).le) (fun _ => by norm_num)
  simp only [← Lax342547.ComponentCharacters.block_factor_phase, Lax342547Proofs.Walsh.sign_add, mul_one,
    Lax342547.ComponentCharacters.block_image_dimension, Nat.cast_mul] at h ⊢
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/--
---
conclusion: Lax342547.ComponentCharacters.retained_component_character_dichotomy
---
-/
theorem retained_component_character_dichotomy {ΩA ΩB Axis N : Type} {I : Axis → Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype Axis] [Fintype N] [∀ a, Fintype (I a)]
    (α : ΩA → ℝ) (β : ΩB → ℝ)
    (X : ΩA → ∀ a, Matrix N (I a) Binary) (Y : ΩB → ∀ a, Matrix N (I a) Binary)
    (D E : ∀ a, Submodule Binary (I a → Binary))
    (T : ∀ a, LinearMap.BilinForm Binary (I a → Binary))
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    (hαsum : ∑ x, α x = 1) (hβsum : ∑ y, β y = 1)
    (hD : ∀ x y a v, v ∈ D a → ∀ w, actualForm (X x a) (Y y a) v w = T a v w)
    (hE : ∀ x y a v w, w ∈ E a → actualForm (X x a) (Y y a) v w = T a v w)
    (hcapA : ∀ (r : Axis → ℕ) (A : ∀ a, Matrix (I a) (Fin (r a)) Binary),
      (∀ a, Function.Injective ((D a).mkQ.comp (A a).mulVecLin)) →
      ∀ x, push α (fun ω => blockImage A (X ω)) x ≤
        (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, r a)*Fintype.card N)))
    (hcapB : ∀ (r : Axis → ℕ) (B : ∀ a, Matrix (I a) (Fin (r a)) Binary),
      (∀ a, Function.Injective ((E a).mkQ.comp (B a).mulVecLin)) →
      ∀ y, push β (fun ω => blockImage B (Y ω)) y ≤
        (2 : ℝ)^(-(95/100 : ℝ)*((∑ a, r a)*Fintype.card N)))
    (C : ∀ a, Matrix (I a) (I a) Binary) : by
      classical
      let mean := ∑ x, ∑ y, α x * β y * sign (∑ a,
        (coefficientPair (C a) (X x a) (Y y a) +
          matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (C a)))
      exact mean = 1 ∨ |mean| ≤ (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card N) := by
  classical
  choose p hp hpk hpid using (fun a =>
    Lax342547.ProjectedCoefficients.exists_quotient_projection (D a))
  choose q hq hqk hqid using (fun a =>
    Lax342547.ProjectedCoefficients.exists_quotient_projection (E a))
  let Z (a : Axis) := (p a).toMatrix' * C a * (q a).toMatrix'.transpose
  have hd (x : ΩA) (y : ΩB) (a : Axis) :
      coefficientPair (C a) (X x a) (Y y a) + matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (C a) =
        coefficientPair (Z a) (X x a) (Y y a) + matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (Z a) :=
    Lax342547.RetainedCharacters.disagreement_projection (C a) (D a) (E a)
      (p a) (q a) (hp a) (hq a) (X x a) (Y y a) (T a)
      (fun v hv w => hD x y a v hv w) (hE x y a)
  by_cases hz : ∀ a, Z a = 0
  · left
    have hzero (x : ΩA) (y : ΩB) : sign (∑ a,
        (coefficientPair (C a) (X x a) (Y y a) +
          matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (C a))) = 1 := by
      simp only [hd, hz]
      simp [coefficientPair, Lax342547Proofs.Walsh.sign_zero]
    simp only [hzero, mul_one, ← Finset.mul_sum, hβsum, hαsum]
  · right
    choose A B hAB hA hB using (fun a =>
      Lax342547.QuotientFactors.quotient_independent_factors (C a) (D a) (E a)
        (p a) (q a) (hpk a) (hqk a) (hpid a) (hqid a))
    let c := ∑ a, matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (Z a)
    have he (x : ΩA) (y : ΩB) : (∑ a,
        (coefficientPair (C a) (X x a) (Y y a) +
          matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (C a))) =
        (∑ a, coefficientPair (A a * (B a).transpose) (X x a) (Y y a)) + c := by
      simp only [hd, hAB]
      exact Finset.sum_add_distrib
    have h := Lax342547.ComponentCharacters.component_character_bound α β X Y A B c hα hβ hαsum.le hβsum.le
      (by simpa only [Fintype.card_fin] using hcapA (fun a => (Z a).rank) A hA)
      (by simpa only [Fintype.card_fin] using hcapB (fun a => (Z a).rank) B hB)
    simp only [← he] at h
    apply h.trans
    have hr : 1 ≤ ∑ a, (Z a).rank := by
      push Not at hz
      obtain ⟨a, ha⟩ := hz
      have hpos : 1 ≤ (Z a).rank := Nat.one_le_iff_ne_zero.mpr
        (fun h => ha (Lax342547.RetainedCharacters.rank_zero_matrix (Z a) h))
      exact hpos.trans (Finset.single_le_sum (fun b _ => Nat.zero_le (Z b).rank) (Finset.mem_univ a))
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    simp only [Fintype.card_fin]
    have hdim : (Fintype.card N : ℝ) ≤ (∑ a, (Z a).rank) * Fintype.card N := by
      exact_mod_cast Nat.le_mul_of_pos_left (Fintype.card N) hr
    nlinarith

end Lax342547Proofs.ComponentCharacters
