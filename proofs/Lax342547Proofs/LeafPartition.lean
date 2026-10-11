import Lax342547.LeafPartition
import Lax342547.LeafExtraction

namespace Lax342547Proofs.LeafPartition

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.LeafExtraction
open Lax342547.LeafPartition
open scoped ENNReal

/--
---
conclusion: Lax342547.LeafPartition.exists_partition
---
Induct on the remaining finite support. If its mass exceeds delta,
extract a nonempty leaf and remove its entire support. The induction
gives disjointness, the residual mass bound, and all original leaf masses.
-/
theorem exists_partition {Ω Axis I N : Type}
    [DecidableEq Ω] [Fintype Axis] [Fintype I] [Fintype N]
    (p : PMF Ω) (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P₀ : Pin Axis I N) (R : Finset Ω) (hR : (R : Set Ω) ⊆ P₀.event A)
    (δ α : ℝ≥0∞) (hα₀ : α ≠ 0) (hαtop : α ≠ ⊤) :
    ∃ L : Finset (Finset Ω × Pin Axis I N), Partition p A P₀ R δ α L := by
  classical
  induction R using Finset.strongInductionOn with
  | _ R ih =>
    by_cases hmass : p.toOuterMeasure (R : Set Ω) ≤ δ
    · refine ⟨∅, ?_⟩
      simpa [Partition] using hmass
    · obtain ⟨P, hext, hmassP, hgood⟩ := Lax342547.LeafExtraction.exists_leaf p A P₀ R hR δ α
        hα₀ hαtop (lt_of_not_ge hmass)
      let S := R.filter (fun o => o ∈ P.event A)
      have hS : (S : Set Ω) = (R : Set Ω) ∩ P.event A := by ext o; simp [S]
      have hSR : S ⊆ R := Finset.filter_subset _ _
      have hSP : (S : Set Ω) ⊆ P.event A := by rw [hS]; exact Set.inter_subset_right
      rw [← hS] at hmassP hgood
      have hSnonempty : S.Nonempty := by
        by_contra he
        have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
        rw [hz, Finset.coe_empty, MeasureTheory.measure_empty] at hmassP
        exact not_lt_of_ge zero_le hmassP
      have hstrict : R \ S ⊂ R := by
        refine ⟨Finset.sdiff_subset, ?_⟩
        obtain ⟨o, ho⟩ := hSnonempty
        intro h
        exact (Finset.mem_sdiff.mp (h (hSR ho))).2 ho
      obtain ⟨L, hL, hdisjoint, hrest⟩ := ih (R \ S) hstrict
        (fun o ho => hR (Finset.mem_sdiff.mp ho).1)
      have hSL (z) (hz : z ∈ L) : Disjoint S z.1 := by
        apply Finset.disjoint_left.mpr
        intro o hoS hoz
        exact (Finset.mem_sdiff.mp ((hL z hz).1 hoz)).2 hoS
      refine ⟨insert (S, P) L, ?_, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact ⟨hSR, hext, hSP, hmassP, hgood⟩
        · obtain ⟨hzR, hzExt, hzPin, hzMass, hzGood⟩ := hL z hz
          exact ⟨fun o ho => (Finset.mem_sdiff.mp (hzR ho)).1, hzExt, hzPin, hzMass, hzGood⟩
      · intro z hz w hw hne
        rcases Finset.mem_insert.mp hz with rfl | hz
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact (hne rfl).elim
          · exact hSL w hw
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact (hSL z hz).symm
          · exact hdisjoint z hz w hw hne
      · have he : R \ (insert (S, P) L).biUnion Prod.fst = (R \ S) \ L.biUnion Prod.fst := by
          ext o
          simp only [Finset.biUnion_insert, Finset.mem_sdiff, Finset.mem_union, not_or]
          tauto
        rwa [he]

end Lax342547Proofs.LeafPartition
