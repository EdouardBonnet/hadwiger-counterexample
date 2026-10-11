import Lax342547.UnaryRowLaw
import Lax342547.ProfileCounting
import Lax342547.CoordinateCounts

/-!
---
title: The finite simultaneous unary mixer estimate
type: lemma
---
The union runs only over nonzero bounded-rank profiles, tags, and labels.
All non-Z fixings are already covered by each individual bad event.
The finite estimate gives a simultaneous choice whenever its explicit
upper bound is below one. No unit law appears in that choice.
-/

namespace Lax342547.UnaryMixers

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.UnaryRowLaw

abbrev Test (k n b degree K : ℕ) :=
  {x : Profile k n b degree // ∑ e, (x.val e).rank ≤ K} × Tag k × (Fin b → Binary)

noncomputable instance (k n b degree K : ℕ) : Fintype (Test k n b degree K) := Fintype.ofFinite _

def Good {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (K s₀ : ℕ)
    (M : Index (Component (Tag k)) J → Moment k n b degree) : Prop :=
  ∀ x : Profile k n b degree, x ≠ 0 → (∑ e, (x.val e).rank ≤ K) →
    ∀ l s, ¬ UnaryBad D x l s s₀ M

def UniformUnary {k n b degree r₀ J : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (K s₀ : ℕ)
    (M : Index (Component (Tag k)) J → Moment k n b degree) : Prop :=
  ∀ x : Profile k n b degree, x ≠ 0 → (∑ e, (x.val e).rank ≤ K) → ∀ l s,
    ∃ W : Submodule Binary (Module.Dual Binary (Fin n → Binary)),
      Module.finrank Binary W ≤ 4 * J * (2 * k) * K ∧
      ∀ z : Base k n → Binary, ∀ hz : ∀ i, i ∉ allowedBase k n l → z i = 0,
        2 * (J - s₀) ≤ (FormalQuadratic.polarMatrix (fun v =>
          gradient D (leftMixers M) (rightMixers M) x (UnaryMixer.atomAlongZ l s z hz v))).rank ∧
        ∀ u v, (∀ a ∈ W, a u = a v) →
          gradient D (leftMixers M) (rightMixers M) x (UnaryMixer.atomAlongZ l s z hz u) =
            gradient D (leftMixers M) (rightMixers M) x (UnaryMixer.atomAlongZ l s z hz v)

noncomputable def testCountBound (k n b degree K : ℕ) : ℕ :=
  ((K + 1) ^ Fintype.card (Component (Tag k)) *
    2 ^ (Fintype.card (Coordinate k n b degree) * K + K * K)) * (2 * k + 1) * 2 ^ b

open scoped ENNReal

noncomputable def failureBound (k n b degree J K s₀ : ℕ) : ℝ≥0∞ :=
  testCountBound k n b degree K *
    (2 ^ (2 * J * K ^ 2 + (s₀ + 1) * (4 * J * (2 * k) * K)) / 2 ^ ((s₀ + 1) * n))

noncomputable def threshold (k b degree J K s₀ : ℕ) : ℕ :=
  (K + 1) ^ Fintype.card (Component (Tag k)) * (2 * k + 1) * 2 ^ b *
    2 ^ ((∑ j ∈ Finset.range (degree + 1), b.choose j) * K + K * K +
      (2 * J * K ^ 2 + (s₀ + 1) * (4 * J * (2 * k) * K)))

axiom failureBound_le_geometric (k n b degree J K s₀ : ℕ)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀) :
    failureBound k n b degree J K s₀ ≤ (threshold k b degree J K s₀ : ℝ≥0∞) / 2 ^ n

axiom uniform_of_good {k n b degree r₀ J K s₀ : ℕ} {hr : 2 * r₀ ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (M : Index (Component (Tag k)) J → Moment k n b degree)
    (hM : Good D K s₀ M) : UniformUnary D K s₀ M

axiom failureBound_lt_one (k n b degree J K s₀ : ℕ)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀)
    (hn : threshold k b degree J K s₀ ≤ n) :
    failureBound k n b degree J K s₀ < 1

axiom simultaneous_failure_bound {k n b degree r₀ J K : ℕ} {hr : 2 * r₀ ≤ n}
    (hk : 0 < k) (D : Testers (k := k) (b := b) (degree := degree) hr) (s₀ : ℕ) :
    (PMF.uniformOfFintype (Index (Component (Tag k)) J → Moment k n b degree)).toOuterMeasure
      {M | ¬ Good D K s₀ M} ≤ failureBound k n b degree J K s₀

axiom exists_of_failureBound_lt_one {k n b degree r₀ J K : ℕ} {hr : 2 * r₀ ≤ n}
    (hk : 0 < k) (D : Testers (k := k) (b := b) (degree := degree) hr) (s₀ : ℕ)
    (hsmall : failureBound k n b degree J K s₀ < 1) :
    ∃ M : Index (Component (Tag k)) J → Moment k n b degree, Good D K s₀ M

axiom exists_for_large_n (k b degree J K s₀ : ℕ) (hk : 0 < k)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∀ r₀ (hr : 2 * r₀ ≤ n)
      (D : Testers (k := k) (b := b) (degree := degree) hr),
      ∃ M : Index (Component (Tag k)) J → Moment k n b degree, Good D K s₀ M

axiom exists_uniform_unary (k b degree J K s₀ : ℕ) (hk : 0 < k)
    (hmargin : (∑ j ∈ Finset.range (degree + 1), b.choose j) * ((2 * k + 1) ^ 2 + 3) * K ≤ s₀) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∀ r₀ (hr : 2 * r₀ ≤ n)
      (D : Testers (k := k) (b := b) (degree := degree) hr),
      ∃ M : Index (Component (Tag k)) J → Moment k n b degree, UniformUnary D K s₀ M

end Lax342547.UnaryMixers
