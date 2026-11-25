import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
---
title: Finite probability tables and cell averages
type: definition
---
All expectations are finite weighted sums. A partition is represented by a map
to a finite set of cells. Cell averages are zero on cells of zero reference mass.
Actual successful queries are subprobability masses; their densities are taken
relative to the reference law. Restricting a query retains its original mass.
-/

namespace Lax793645.FiniteProbability
noncomputable section
open scoped BigOperators

abbrev Weight (A : Type*) := A → ℝ
def indicator (P : Prop) : ℝ := @ite ℝ P (Classical.propDecidable _) 1 0
def expectation {A : Type*} [Fintype A] (μ f : Weight A) : ℝ := ∑ x, μ x * f x
def mass {A : Type*} [Fintype A] (μ : Weight A) (P : A → Prop) : ℝ :=
  expectation μ (fun x => indicator (P x))
def Probability {A : Type*} [Fintype A] (μ : Weight A) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1
def Subprobability {A : Type*} [Fintype A] (μ : Weight A) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x ≤ 1
def product {A B : Type*} (μ : Weight A) (ν : Weight B) : Weight (A × B) :=
  fun x => μ x.1 * ν x.2
def pushforward {A B : Type*} [Fintype A] (μ : Weight A) (p : A → B) : Weight B :=
  fun c => mass μ (fun x => p x = c)
def inner {A : Type*} [Fintype A] (μ f g : Weight A) : ℝ :=
  expectation μ (fun x => f x * g x)
def project {A B : Type*} [Fintype A] (μ : Weight A) (p : A → B)
    (f : Weight A) : Weight A :=
  fun x => pushforward (fun y => μ y * f y) p (p x) / pushforward μ p (p x)
def density {A : Type*} (μ x : Weight A) : Weight A := fun a => x a / μ a
def dominatedSupport {A : Type*} (x μ : Weight A) : Prop :=
  ∀ a, x a ≠ 0 → μ a ≠ 0
def bounded {A : Type*} (f : Weight A) : Prop := (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1)
def l1 {A : Type*} [Fintype A] (x y : Weight A) : ℝ := ∑ a, |x a - y a|
def clip {A : Type*} (R : ℝ) (μ x : Weight A) : Weight A :=
  fun a => min (max (density μ x a) 0) R
def projectionError {A B : Type*} [Fintype A]
    (μ f g : Weight A) (p : A → B) : ℝ :=
  inner μ f g - inner μ (project μ p f) (project μ p g)
def tail {A : Type*} [Fintype A] (R : ℝ) (μ x : Weight A) : ℝ :=
  mass x (fun a => R ≤ density μ x a)
def cellError {A B : Type*} [Fintype A] [Fintype B]
    (μ : Weight A) (p : A → B) (f x : Weight A) : ℝ :=
  l1 (pushforward (fun a => μ a * f a) p) (pushforward x p)
def HasNet {A : Type*} [Fintype A] (P : Weight A → Prop) (r : ℕ) (ε : ℝ) : Prop :=
  ∃ t : ℕ, t ≤ r ∧ ∃ f : Fin t → Weight A, ∀ x, P x → ∃ i, l1 x (f i) ≤ ε

end
end Lax793645.FiniteProbability
