import Lax342547.RetainedCharacters

/-!
---
title: Simultaneous agreement of linear cross Gram tests on retained cells
type: lemma
---
Expand the actual family of scalar Gram tests into coefficient characters. Frozen agreement and all-rank conditional image caps imply agreement of the entire family at cost two to the number of tests plus one.
-/

namespace Lax342547.ScalarGramAgreement

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.ConcreteGeometry
open Lax342547.CoefficientPhase Lax342547.PushforwardWalsh Lax342547.RetainedCharacters
open Lax342547.FourierTests

noncomputable def coefficient {I S : Type} [Fintype S]
    (tests : S → Matrix I I Binary) (t : S → Binary) : Matrix I I Binary :=
  ∑ s, t s • tests s

noncomputable def actualBits {I S N : Type} [Fintype I] [Fintype N]
    (tests : S → Matrix I I Binary) (X Y : Matrix N I Binary) : S → Binary :=
  fun s => coefficientPair (tests s) X Y

noncomputable def targetBits {I S : Type} [Fintype I]
    (tests : S → Matrix I I Binary) (T : LinearMap.BilinForm Binary (I → Binary)) : S → Binary := by
  classical
  exact fun s => matrixPair (LinearMap.BilinForm.toMatrix' T) (tests s)

axiom coefficient_character {I S N : Type} [Fintype I] [Fintype S] [Fintype N]
    (tests : S → Matrix I I Binary) (t : S → Binary) (X Y : Matrix N I Binary)
    (T : LinearMap.BilinForm Binary (I → Binary)) : by
      classical
      exact phase t (actualBits tests X Y) * phase t (targetBits tests T) =
        sign (coefficientPair (coefficient tests t) X Y +
          matrixPair (LinearMap.BilinForm.toMatrix' T) (coefficient tests t))

axiom scalar_gram_agreement {ΩA ΩB I S N : Type}
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
        (fun ab => actualBits tests (X ab.1) (Y ab.2)) (targetBits tests T)

end Lax342547.ScalarGramAgreement
