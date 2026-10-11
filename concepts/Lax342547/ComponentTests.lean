import Lax342547.ComponentCharacters
import Lax342547.ScalarGramAgreement

/-!
---
title: Simultaneous scalar Gram agreement across components
type: lemma
---
A complete scalar test family expands to componentwise coefficient characters. Joint retained-cell image caps and frozen agreement imply simultaneous equality at cost two to the number of tests plus one.
-/

namespace Lax342547.ComponentTests

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.ConcreteGeometry
open Lax342547.CoefficientPhase Lax342547.PushforwardWalsh Lax342547.RetainedCharacters
open Lax342547.ComponentCharacters Lax342547.FourierTests

noncomputable def coefficient {Axis S : Type} {I : Axis → Type} [Fintype S]
    (tests : S → ∀ a, Matrix (I a) (I a) Binary) (t : S → Binary)
    (a : Axis) : Matrix (I a) (I a) Binary := ∑ s, t s • tests s a

noncomputable def actualBits {Axis S N : Type} {I : Axis → Type}
    [Fintype Axis] [Fintype N] [∀ a, Fintype (I a)]
    (tests : S → ∀ a, Matrix (I a) (I a) Binary)
    (X Y : ∀ a, Matrix N (I a) Binary) : S → Binary :=
  fun s => ∑ a, coefficientPair (tests s a) (X a) (Y a)

noncomputable def targetBits {Axis S : Type} {I : Axis → Type}
    [Fintype Axis] [∀ a, Fintype (I a)]
    (tests : S → ∀ a, Matrix (I a) (I a) Binary)
    (T : ∀ a, LinearMap.BilinForm Binary (I a → Binary)) : S → Binary := by
  classical
  exact fun s => ∑ a, matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (tests s a)

axiom coefficient_character {Axis S N : Type} {I : Axis → Type}
    [Fintype Axis] [Fintype S] [Fintype N] [∀ a, Fintype (I a)]
    (tests : S → ∀ a, Matrix (I a) (I a) Binary) (t : S → Binary)
    (X Y : ∀ a, Matrix N (I a) Binary)
    (T : ∀ a, LinearMap.BilinForm Binary (I a → Binary)) : by
      classical
      exact phase t (actualBits tests X Y) * phase t (targetBits tests T) =
        sign (∑ a, (coefficientPair (coefficient tests t a) (X a) (Y a) +
          matrixPair (LinearMap.BilinForm.toMatrix' (T a)) (coefficient tests t a)))

axiom component_scalar_agreement {ΩA ΩB Axis N : Type} {I : Axis → Type} {S : Type}
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
        (fun ab => actualBits tests (X ab.1) (Y ab.2)) (targetBits tests T)

end Lax342547.ComponentTests
