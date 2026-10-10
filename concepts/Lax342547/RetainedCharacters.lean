import Lax342547.QuotientFactors
import Lax342547.CoefficientPhase
import Lax342547.FrozenRecords

/-!
---
title: Actual cross Gram characters on frozen unary cells
type: definition and theorem
---
Frozen agreement removes every frozen-factor coefficient term. Quotient rank factors and conditional image caps give the exact zero-character versus .45N bias alternative for actual cross Gram characters.
-/

namespace Lax342547.RetainedCharacters

open Lax342547.MomentSpace Lax342547.Walsh Lax342547.ConcreteGeometry
open Lax342547.CoefficientPhase Lax342547.PushforwardWalsh

noncomputable def actualForm {I N : Type} [Fintype I] [Fintype N]
    (X Y : Matrix N I Binary) : LinearMap.BilinForm Binary (I → Binary) := by
  classical
  exact (X.transpose * Y).toBilin'

axiom coefficient_pair_form {I N : Type} [Fintype I] [Fintype N]
    (C : Matrix I I Binary) (X Y : Matrix N I Binary) : by
      classical
      exact coefficientPair C X Y = matrixPair (LinearMap.BilinForm.toMatrix' (actualForm X Y)) C

axiom binary_self_add (z : Binary) : z + z = 0

axiom disagreement_projection {I N : Type} [Fintype I] [Fintype N]
    (C : Matrix I I Binary) (D E : Submodule Binary (I → Binary))
    (p q : (I → Binary) →ₗ[Binary] (I → Binary))
    (hp : D.mkQ.comp p = D.mkQ) (hq : E.mkQ.comp q = E.mkQ)
    (X Y : Matrix N I Binary) (T : LinearMap.BilinForm Binary (I → Binary))
    (hD : ∀ v ∈ D, ∀ w, actualForm X Y v w = T v w)
    (hE : ∀ v w, w ∈ E → actualForm X Y v w = T v w) : by
      classical
      let Z := p.toMatrix' * C * q.toMatrix'.transpose
      exact coefficientPair C X Y + matrixPair (LinearMap.BilinForm.toMatrix' T) C =
        coefficientPair Z X Y + matrixPair (LinearMap.BilinForm.toMatrix' T) Z

axiom sign_abs (z : Binary) : |sign z| = 1

axiom rank_zero_matrix {I J : Type} [Fintype I] [Fintype J]
    (C : Matrix I J Binary) (h : C.rank = 0) : C = 0

axiom retained_character_dichotomy {ΩA ΩB I N : Type}
    [Fintype ΩA] [Fintype ΩB] [Fintype I] [Fintype N]
    (α : ΩA → ℝ) (β : ΩB → ℝ)
    (X : ΩA → Matrix N I Binary) (Y : ΩB → Matrix N I Binary)
    (D E : Submodule Binary (I → Binary)) (T : LinearMap.BilinForm Binary (I → Binary))
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
    (C : Matrix I I Binary) : by
      classical
      let mean := ∑ a, ∑ b, α a * β b *
        sign (coefficientPair C (X a) (Y b) + matrixPair (LinearMap.BilinForm.toMatrix' T) C)
      exact mean = 1 ∨ |mean| ≤ (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card N)

end Lax342547.RetainedCharacters
