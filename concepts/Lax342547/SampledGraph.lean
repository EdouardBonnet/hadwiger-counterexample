import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
---
title: Graphs sampled from a hole relation
type: lemma
---
Given a symmetric relation of holes and a list of raw vertices, join two
distinct positions exactly when their entries have no hole. Repeated raw
vertices are permitted. If the hole relation has no triangles, every
independent set of the sampled graph has size at most two, as in (2.2).
-/

namespace Lax342547.SampledGraph

universe u

def sampleGraph {Ω : Type u} (hole : Ω → Ω → Prop) (hsymm : (∀ ⦃i j⦄, hole i j → hole j i))
    {m : ℕ} (sample : Fin m → Ω) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ ¬ hole (sample i) (sample j)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, fun h' ↦ h.2 (hsymm h')⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

axiom sampleGraph_indepNum_le_two {Ω : Type u}
    (hole : Ω → Ω → Prop) (hsymm : (∀ ⦃i j⦄, hole i j → hole j i))
    (htriangle : ∀ i j k, hole i j → hole j k → ¬ hole k i)
    {m : ℕ} (sample : Fin m → Ω) :
    (sampleGraph hole hsymm sample).indepNum ≤ 2

end Lax342547.SampledGraph
