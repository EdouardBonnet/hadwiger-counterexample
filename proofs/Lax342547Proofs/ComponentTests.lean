import Lax342547.ComponentTests
import Lax342547Proofs.ComponentCharacters
import Lax342547Proofs.ScalarGramAgreement

namespace Lax342547Proofs.ComponentTests
open Lax342547.ComponentTests

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.ConcreteGeometry
open Lax342547.CoefficientPhase Lax342547.PushforwardWalsh Lax342547.RetainedCharacters
open Lax342547.ComponentCharacters Lax342547.FourierTests

/--
---
conclusion: Lax342547.ComponentTests.coefficient_character
---
-/
theorem coefficient_character {Axis S N : Type} {I : Axis → Type}
    [Fintype Axis] [Fintype S] [Fintype N] [∀ a, Fintype (I a)]
    (tests : S → ∀ a, Matrix (I a) (I a) Binary) (t : S → Binary)
    (X Y : ∀ a, Matrix N (I a) Binary)
    (T : ∀ a, LinearMap.BilinForm Binary (I a → Binary)) : by
      classical
      exact phase t (actualBits tests X Y) * phase t (targetBits tests T) =
        sign (∑ a, (coefficientPair (coefficient tests t a) (X a) (Y a) +
          matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (coefficient tests t a))) := by
  classical
  have ha : dotProduct t (actualBits tests X Y) =
      ∑ a, coefficientPair (coefficient tests t a) (X a) (Y a) := by
    simp only [Lax342547Proofs.RetainedCharacters.coefficient_pair_form,
      coefficient, map_sum, map_smul, smul_eq_mul]
    unfold dotProduct actualBits
    simp only [Finset.mul_sum, Lax342547Proofs.RetainedCharacters.coefficient_pair_form]
    rw [Finset.sum_comm]
  have hb : dotProduct t (targetBits tests T) =
      ∑ a, matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (coefficient tests t a) := by
    simp only [coefficient, map_sum, map_smul, smul_eq_mul, dotProduct, targetBits, Finset.mul_sum]
    rw [Finset.sum_comm]
  unfold phase
  rw [← Lax342547Proofs.Walsh.sign_add, ha, hb, ← Finset.sum_add_distrib]

/--
---
conclusion: Lax342547.ComponentTests.component_scalar_agreement
---
-/
theorem component_scalar_agreement {ΩA ΩB Axis N : Type} {I : Axis → Type} {S : Type}
    [Fintype S] [Fintype ΩA] [Fintype ΩB] [Fintype Axis] [Fintype N] [∀ a, Fintype (I a)]
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
    (tests : S → ∀ a, Matrix (I a) (I a) Binary)
    (hsmall : (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card N) ≤
      1 / (2 : ℝ)^(Fintype.card S + 1)) :
    1 / (2 : ℝ)^(Fintype.card S + 1) ≤
      patternMass (fun ab : ΩA × ΩB => α ab.1 * β ab.2)
        (fun ab => actualBits tests (X ab.1) (Y ab.2)) (targetBits tests T) := by
  classical
  apply Lax342547Proofs.GramTests.zero_or_biased_agreement _ _ _ _
    (Real.rpow_pos_of_pos (by norm_num) _).le _ _ hsmall
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum, hβsum, mul_one, hαsum]
  · intro t _
    have h := Lax342547Proofs.ComponentCharacters.retained_component_character_dichotomy
      α β X Y D E T hα hβ hαsum hβsum hD hE hcapA hcapB (coefficient tests t)
    have he : characterMean (fun ab : ΩA × ΩB => α ab.1 * β ab.2)
        (fun ab => actualBits tests (X ab.1) (Y ab.2)) (targetBits tests T) t =
        ∑ x, ∑ y, α x * β y * sign (∑ a,
          (coefficientPair (coefficient tests t a) (X x a) (Y y a) +
            matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (coefficient tests t a))) := by
      unfold characterMean
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [mul_assoc, coefficient_character]
    rw [he]
    exact h

end Lax342547Proofs.ComponentTests
