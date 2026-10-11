import Lax342547.SecondPeeling
import Lax342547.ReferencePins

/-!
---
title: Second exact-pin peeling for the actual raw frame law
type: lemma
---
After a retained restriction of an old leaf, split by bounded coefficient
metadata and exact images. Discard exponentially small mass and apply a
fresh peeling on every retained fiber, within the paper's final budget.
-/

namespace Lax342547.RawSecondPeeling

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins
open Lax342547.ReferencePins Lax342547.MetadataPins Lax342547.SecondPeeling
open scoped ENNReal

axiom raw_second_peeling {J Comp B H N : Type}
    [Fintype J] [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)] [DecidableEq (Frame B H N E)]
    (p : PMF (Fin 2 → Comp → Frame B H N E))
    (P₀ : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (S : Set (Fin 2 → Comp → Frame B H N E)) (hS : ∃ o ∈ S, o ∈ p.support)
    (choice : (Fin 2 → Comp → Frame B H N E) → J)
    (U : J → (Comp × Bool) → Submodule Binary ((Fin 2 × (B ⊕ H)) → Binary))
    (D ζ ε : ℝ) (K₁ u a n : ℕ)
    (hD : 0 ≤ D) (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : 0 < ε) (hεζ : ε ≤ ζ / 4)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hcoeff : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ ε * Fintype.card N)
    (hcomp : (8 : ℝ) * Fintype.card Comp ≤ ε * Fintype.card N)
    (hP : p.support ⊆ P₀.event observation) (hPbudget : P₀.rank ≤ K₁)
    (hu : ∀ j, ∑ b, Module.finrank Binary (U j b) ≤ u)
    (hchoices : Fintype.card J ≤ 2 ^ (a * n)) (hscale : 2 * a * n ≤ Fintype.card N)
    (hSbound : (2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)) ≤ p.toOuterMeasure S)
    (hp : ∀ o, p o ≤ (2 : ℝ≥0∞) ^ ((D + K₁ + 1) * Fintype.card N) * PMF.uniformOfFintype _ o) :
    (p.filter S hS).toOuterMeasure {o |
      (p.filter S hS).toOuterMeasure {x | record observation choice U x = record observation choice U o} <
        (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N))} ≤
      (2 : ℝ≥0∞) ^ (-(Fintype.card N : ℝ) / 2) ∧
    ∀ k : Key N U,
      (2 : ℝ≥0∞) ^ (-(((u : ℝ) + 1) * Fintype.card N)) ≤
        (p.filter S hS).toOuterMeasure {o | record observation choice U o = k} →
      RepeeledPart (p.filter S hS) (PMF.uniformOfFintype _) observation P₀ choice U D ζ K₁ u k

end Lax342547.RawSecondPeeling
