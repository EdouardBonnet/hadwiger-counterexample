import Lax342547.RawSecondPeeling
import Lax342547.ReferencePins
import Lax342547.SecondPeeling
import Lax342547.SplitTrimming

namespace Lax342547Proofs.RawSecondPeeling

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins
open Lax342547.ReferencePins Lax342547.MetadataPins Lax342547.SecondPeeling
open scoped ENNReal

/--
---
conclusion: Lax342547.RawSecondPeeling.raw_second_peeling
---
Use the exact metadata/image record count to bound discarded fibers.
On every retained fiber, the unconditional raw reference cap supplies
the fresh peeling with its required all-rank estimate. All old pins and
deliberately added images are preserved within the final total budget.
-/
theorem raw_second_peeling {J Comp B H N : Type}
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
      RepeeledPart (p.filter S hS) (PMF.uniformOfFintype _) observation P₀ choice U D ζ K₁ u k := by
  refine ⟨Lax342547.SplitTrimming.exponential_discard (p.filter S hS) observation choice U a n u
    hchoices hu hscale, ?_⟩
  intro k hk
  exact Lax342547.SecondPeeling.second_part p (PMF.uniformOfFintype _) observation P₀ S hS choice U
    D ζ ε K₁ u hD hζ hζ₁ hεζ (by omega) hP hPbudget hu hSbound hp
    (Lax342547.ReferencePins.reference_pin_cap ε hε hN hcoeff hcomp) k hk

end Lax342547Proofs.RawSecondPeeling
