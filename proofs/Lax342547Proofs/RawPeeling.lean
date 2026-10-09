import Lax342547.RawPeeling
import Lax342547Proofs.BoundedPeeling
import Lax342547Proofs.ReferencePins

namespace Lax342547Proofs.RawPeeling

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins
open Lax342547.ReferencePins Lax342547.LeafPartition Lax342547.BoundedPeeling
open scoped ENNReal

/--
---
conclusion: Lax342547.RawPeeling.raw_peeling
---
The reference pin cap is the checked all-rank raw image cap. Substituting
it in bounded peeling gives a disjoint partition, preserves all initial
images, and bounds the total dimension by the initial rank plus K. The
normalized leaves retain the quantitative joint density and image bounds.
-/
theorem raw_peeling {Comp B H N : Type}
    [Fintype Comp] [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq Comp] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)] [DecidableEq (Frame B H N E)]
    (σ : PMF (Fin 2 → Comp → Frame B H N E))
    (P₀ : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (R : Finset (Fin 2 → Comp → Frame B H N E))
    (hR : (R : Set (Fin 2 → Comp → Frame B H N E)) ⊆ P₀.event observation)
    (D ζ ε : ℝ) (K : ℕ)
    (hζ : 0 < ζ) (hζ₁ : ζ ≤ 1) (hε : 0 < ε) (hεζ : ε ≤ ζ / 4)
    (hK : 4 * (D + 1) / ζ ≤ K)
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (hp : (4 : ℝ) * (Fintype.card B + Fintype.card H : ℕ) ≤ ε * Fintype.card N)
    (hc : (8 : ℝ) * Fintype.card Comp ≤ ε * Fintype.card N)
    (hσ : ∀ o, σ o ≤ (2 : ℝ≥0∞) ^ (D * Fintype.card N) * PMF.uniformOfFintype _ o) :
    ∃ L : Finset (Finset (Fin 2 → Comp → Frame B H N E) × Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N),
      Partition σ observation P₀ R ((2 : ℝ≥0∞) ^ (-(ζ * Fintype.card N)))
        ((2 : ℝ≥0∞) ^ (-((1 - ζ) * Fintype.card N))) L ∧
      ∀ z ∈ L, z.2.rank ≤ P₀.rank + K ∧
        LawBound σ (PMF.uniformOfFintype _) observation z.2 z.1
          ((2 : ℝ≥0∞) ^ (-((1 - ζ) * Fintype.card N)))
          ((2 : ℝ≥0∞) ^ ((D + K + 1) * Fintype.card N)) := by
  obtain ⟨L, hL, hbound⟩ := BoundedPeeling.bounded_partition σ (PMF.uniformOfFintype _)
    observation P₀ R hR D ζ ε (Fintype.card N) K (by omega) hζ hζ₁ hεζ hK hσ
    (ReferencePins.reference_pin_cap ε hε hN hp hc)
  refine ⟨L, hL, fun z hz => ?_⟩
  obtain ⟨hrank, hlaw⟩ := hbound z hz
  exact ⟨by omega, hlaw⟩

end Lax342547Proofs.RawPeeling
