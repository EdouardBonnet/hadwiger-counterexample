import Lax342547.RetainedCharacters

/-!
---
title: Joint retained-cell characters across all components
type: lemma
---
Componentwise quotient projections and rank factors combine into one joint Walsh image. No independence between components or nominal orientations is imposed; rank sums control the complete character.
-/

namespace Lax342547.ComponentCharacters

open Lax342547.ConcreteGeometry
open Lax342547.MomentSpace Lax342547.Walsh Lax342547.CoefficientPhase
open Lax342547.PushforwardWalsh Lax342547.RetainedCharacters

noncomputable def blockImage {Axis N : Type} {I R : Axis → Type}
    [Fintype N] [∀ a, Fintype (I a)]
    (A : ∀ a, Matrix (I a) (R a) Binary) (X : ∀ a, Matrix N (I a) Binary) :
    ((Σ a, R a) × N) → Binary := fun v => factorImage (A v.1.1) (X v.1.1) (v.1.2,v.2)

axiom block_factor_pair {Axis N : Type} {I R : Axis → Type}
    [Fintype Axis] [Fintype N] [∀ a, Fintype (I a)] [∀ a, Fintype (R a)]
    (A B : ∀ a, Matrix (I a) (R a) Binary) (X Y : ∀ a, Matrix N (I a) Binary) :
    (∑ a, coefficientPair (A a * (B a).transpose) (X a) (Y a)) =
      dotProduct (blockImage A X) (blockImage B Y)

axiom block_factor_phase {Axis N : Type} {I R : Axis → Type}
    [Fintype Axis] [Fintype N] [∀ a, Fintype (I a)] [∀ a, Fintype (R a)]
    (A B : ∀ a, Matrix (I a) (R a) Binary) (X Y : ∀ a, Matrix N (I a) Binary) :
    sign (∑ a, coefficientPair (A a * (B a).transpose) (X a) (Y a)) =
      phase (blockImage A X) (blockImage B Y)

axiom block_image_dimension {Axis N : Type} {R : Axis → Type}
    [Fintype Axis] [Fintype N] [∀ a, Fintype (R a)] :
    Fintype.card ((Σ a, R a) × N) = (∑ a, Fintype.card (R a)) * Fintype.card N

axiom component_character_bound {ΩA ΩB Axis N : Type} {I R : Axis → Type}
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
      (2 : ℝ)^(-(45/100 : ℝ)*((∑ a, Fintype.card (R a))*Fintype.card N))

axiom retained_component_character_dichotomy {ΩA ΩB Axis N : Type} {I : Axis → Type}
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
      exact mean = 1 ∨ |mean| ≤ (2 : ℝ)^(-(45/100 : ℝ)*Fintype.card N)

end Lax342547.ComponentCharacters
