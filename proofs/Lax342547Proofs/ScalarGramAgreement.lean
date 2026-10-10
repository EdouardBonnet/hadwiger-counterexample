import Lax342547.ScalarGramAgreement
import Lax342547Proofs.RetainedCharacters

namespace Lax342547Proofs.ScalarGramAgreement
open Lax342547.ScalarGramAgreement

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.ConcreteGeometry
open Lax342547.CoefficientPhase Lax342547.PushforwardWalsh Lax342547.RetainedCharacters
open Lax342547.FourierTests

/--
---
conclusion: Lax342547.ScalarGramAgreement.coefficient_character
---
-/
theorem coefficient_character {I S N : Type} [Fintype I] [Fintype S] [Fintype N]
    (tests : S → Matrix I I Binary) (t : S → Binary) (X Y : Matrix N I Binary)
    (T : LinearMap.BilinForm Binary (I → Binary)) : by
      classical
      exact phase t (actualBits tests X Y) * phase t (targetBits tests T) =
        sign (coefficientPair (coefficient tests t) X Y +
          matrixPair (LinearMap.BilinForm.toMatrix' T) (coefficient tests t)) := by
  classical
  have ha : dotProduct t (actualBits tests X Y) = coefficientPair (coefficient tests t) X Y := by
    rw [Lax342547Proofs.RetainedCharacters.coefficient_pair_form]
    simp only [coefficient, map_sum, map_smul, smul_eq_mul]
    unfold dotProduct actualBits
    apply Finset.sum_congr rfl
    intro s _
    rw [Lax342547Proofs.RetainedCharacters.coefficient_pair_form]
  have hb : dotProduct t (targetBits tests T) =
      matrixPair (LinearMap.BilinForm.toMatrix' T) (coefficient tests t) := by
    simp only [coefficient, map_sum, map_smul, smul_eq_mul, dotProduct, targetBits]
  unfold phase
  rw [← Lax342547Proofs.Walsh.sign_add, ha, hb]

/--
---
conclusion: Lax342547.ScalarGramAgreement.scalar_gram_agreement
---
-/
theorem scalar_gram_agreement {ΩA ΩB I S N : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype I] [Fintype S] [Fintype N]
    (α : ΩA → ℝ) (β : ΩB → ℝ)
    (X : ΩA → Matrix N I Binary) (Y : ΩB → Matrix N I Binary)
    (D E : Submodule Binary (I → Binary)) (T : LinearMap.BilinForm Binary (I → Binary))
    (tests : S → Matrix I I Binary)
    (hα : ∀ a, 0 ≤ α a) (hβ : ∀ b, 0 ≤ β b)
    (hαsum : ∑ a, α a = 1) (hβsum : ∑ b, β b = 1)
    (hD : ∀ a b v, v ∈ D → ∀ w, actualForm (X a) (Y b) v w = T v w)
    (hE : ∀ a b v w, w ∈ E → actualForm (X a) (Y b) v w = T v w)
    (hcapA : ∀ r (A : Matrix I (Fin r) Binary), Function.Injective (D.mkQ.comp A.mulVecLin) →
      ∀ x, push α (fun a => factorImage A (X a)) x ≤
        (2 : ℝ)^(-(95/100 : ℝ)*(r * Fintype.card N)))
    (hcapB : ∀ r (B : Matrix I (Fin r) Binary), Function.Injective (E.mkQ.comp B.mulVecLin) →
      ∀ y, push β (fun b => factorImage B (Y b)) y ≤
        (2 : ℝ)^(-(95/100 : ℝ)*(r * Fintype.card N)))
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
    have h := Lax342547Proofs.RetainedCharacters.retained_character_dichotomy
      α β X Y D E T hα hβ hαsum hβsum hD hE hcapA hcapB (coefficient tests t)
    have he : characterMean (fun ab : ΩA × ΩB => α ab.1 * β ab.2)
        (fun ab => actualBits tests (X ab.1) (Y ab.2)) (targetBits tests T) t =
        ∑ a, ∑ b, α a * β b * sign (coefficientPair (coefficient tests t) (X a) (Y b) +
          matrixPair (LinearMap.BilinForm.toMatrix' T) (coefficient tests t)) := by
      unfold characterMean
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [mul_assoc, coefficient_character]
    rw [he]
    exact h

end Lax342547Proofs.ScalarGramAgreement
