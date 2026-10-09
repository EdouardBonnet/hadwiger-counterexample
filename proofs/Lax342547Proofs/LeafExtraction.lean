import Lax342547.LeafExtraction
import Lax342547Proofs.ExactPins
import Mathlib.Data.Finset.Max

namespace Lax342547Proofs.LeafExtraction

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.LeafExtraction
open scoped ENNReal

/--
---
conclusion: Lax342547.LeafExtraction.exists_leaf
---
Choose an admissible extension of maximal nominal rank, retaining the
strict mass lower bound. If a positive-rank test violates the desired
relative cap, its nonempty intersection supplies a consistent join. The
rank and mass identities make that join a larger admissible extension.
-/
theorem exists_leaf {Ω Axis I N : Type}
    [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Set Ω) (hR : R ⊆ P₀.event A)
    (δ α : ℝ≥0∞) (hα₀ : α ≠ 0) (hαtop : α ≠ ⊤) (hmass : δ < p.toOuterMeasure R) :
    ∃ P : Pin Axis I N, P₀.Extends P ∧
      δ * α ^ (P.rank - P₀.rank) < p.toOuterMeasure (R ∩ P.event A) ∧
      Good p A P (R ∩ P.event A) α := by
  classical
  let T := Finset.univ.filter (fun P : Pin Axis I N => P₀.Extends P ∧
    δ * α ^ (P.rank - P₀.rank) < p.toOuterMeasure (R ∩ P.event A))
  have hstart : P₀ ∈ T := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ExactPins.extends_refl P₀, ?_⟩
    simpa only [Nat.sub_self, pow_zero, mul_one, Set.inter_eq_left.mpr hR] using hmass
  obtain ⟨P, hP, hmax⟩ := Finset.exists_max_image T Pin.rank ⟨P₀, hstart⟩
  obtain ⟨hext, hmassP⟩ := (Finset.mem_filter.mp hP).2
  refine ⟨P, hext, hmassP, fun Q hQ => ?_⟩
  by_contra hn
  have hbad := lt_of_not_ge hn
  have hnonempty : ((R ∩ P.event A) ∩ Q.event A).Nonempty := by
    by_contra he
    have hz := Set.not_nonempty_iff_eq_empty.mp he
    rw [hz, MeasureTheory.measure_empty] at hbad
    exact not_lt_of_ge zero_le hbad
  obtain ⟨o, ho⟩ := hnonempty
  have hrefine := ExactPins.event_refinement A P Q o ⟨ho.1.2, ho.2⟩
  have hrank := ExactPins.rank_refinement A P Q o
  have hmono := ExactPins.rank_mono P₀ P hext
  have hdifference : (P.joinAt A Q o).rank - P₀.rank =
      (P.rank - P₀.rank) + P.relativeRank Q := by omega
  have hnewmass : δ * α ^ ((P.joinAt A Q o).rank - P₀.rank) <
      p.toOuterMeasure (R ∩ (P.joinAt A Q o).event A) := by
    rw [hdifference, pow_add, hrefine.2.2, ← Set.inter_assoc]
    have hmul := ENNReal.mul_lt_mul_right (pow_ne_zero (P.relativeRank Q) hα₀)
      (ENNReal.pow_ne_top hαtop) hmassP
    apply lt_trans ?_ hbad
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hnew : P.joinAt A Q o ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ExactPins.extends_trans hext hrefine.1, hnewmass⟩
  have hb := hmax _ hnew
  omega

end Lax342547Proofs.LeafExtraction
