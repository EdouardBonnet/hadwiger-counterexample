import Lax342547.SampledGraph

namespace Lax342547Proofs.SampledGraph

open Lax342547.SampledGraph

universe u

theorem independent_set_card_le_two {Ω : Type u}
    (hole : Ω → Ω → Prop) (hsymm : (∀ ⦃i j⦄, hole i j → hole j i))
    (htriangle : ∀ i j k, hole i j → hole j k → ¬ hole k i)
    {m : ℕ} (sample : Fin m → Ω) (S : Finset (Fin m))
    (hS : (sampleGraph hole hsymm sample).IsIndepSet (S : Set (Fin m))) :
    S.card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
  have hhij : hole (sample i) (sample j) := by
    by_contra h'
    exact hS hi hj hij ⟨hij, h'⟩
  have hhjk : hole (sample j) (sample k) := by
    by_contra h'
    exact hS hj hk hjk ⟨hjk, h'⟩
  have hhki : hole (sample k) (sample i) := by
    by_contra h'
    exact hS hk hi hik.symm ⟨hik.symm, h'⟩
  exact htriangle _ _ _ hhij hhjk hhki

/--
---
conclusion: Lax342547.SampledGraph.sampleGraph_indepNum_le_two
---
Three independent sample positions would produce three pairwise holes.
This argument does not require the sampled raw vertices to be distinct.
-/
theorem sampleGraph_indepNum_le_two {Ω : Type u}
    (hole : Ω → Ω → Prop) (hsymm : (∀ ⦃i j⦄, hole i j → hole j i))
    (htriangle : ∀ i j k, hole i j → hole j k → ¬ hole k i)
    {m : ℕ} (sample : Fin m → Ω) :
    (sampleGraph hole hsymm sample).indepNum ≤ 2 := by
  obtain ⟨S, hS⟩ := (sampleGraph hole hsymm sample).exists_isNIndepSet_indepNum
  have h := independent_set_card_le_two hole hsymm htriangle sample S hS.1
  simpa [hS.2] using h

end Lax342547Proofs.SampledGraph
