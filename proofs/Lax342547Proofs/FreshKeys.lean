import Lax342547.FreshKeys
import Lax342547Proofs.TableSpaces
import Lax342547Proofs.SparsePins

namespace Lax342547Proofs.FreshKeys

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

/--
---
conclusion: Lax342547.FreshKeys.fresh_points
---
Absorb each scalar coefficient into the base evaluation vector and apply
the uniform sparse-label exclusion. Its constant coordinate is exactly
that scalar, so a nonzero coefficient would force a forbidden label.
-/
theorem fresh_points {Base Comp : Type} [Fintype Base] [Fintype Comp] {b degree K R : ℕ}
    (U : Bool → Comp → Submodule Binary (SelectorCoordinates b degree × Option Base → Binary))
    (hdim : ∀ sign e, Module.finrank Binary (U sign e) ≤ K)
    (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ B : Finset (Fin b → Binary),
      B.card ≤ 2 * Fintype.card Comp * K * (R + 14) ∧
      ∀ sign e (L : Finset (Fin b → Binary)) (c : (Fin b → Binary) → Binary)
        (z : (Fin b → Binary) → Base → Binary),
        L.card ≤ R + 14 → Disjoint L B →
        (∑ s ∈ L, c s • point (selectorEval (degree := degree)) s (z s)) ∈ U sign e →
        ∀ s ∈ L, c s = 0 := by
  classical
  obtain ⟨B, hB, hcover⟩ := SparsePins.sparse_pin_labels_finset U hdim hdegree
  refine ⟨B, hB, ?_⟩
  intro sign e L c z hL hdis hmem s hs
  by_contra hcs
  have hvec : c s • baseEval (z s) ≠ 0 := by
    intro hz
    have := congrFun hz none
    exact hcs (by simpa [baseEval] using this)
  have heq (t : Fin b → Binary) :
      Lax342547.SparsePins.labelTensor (selectorEval (degree := degree)) t
          (c t • baseEval (z t)) =
        c t • point (selectorEval (degree := degree)) t (z t) := by
    ext x
    simp [Lax342547.SparsePins.labelTensor, point]
  have hmem' : (∑ t ∈ L, Lax342547.SparsePins.labelTensor (selectorEval (degree := degree)) t
      (c t • baseEval (z t))) ∈ U sign e := by
    simpa only [heq] using hmem
  exact Finset.disjoint_left.mp hdis hs
    (hcover sign e L (fun t => c t • baseEval (z t)) hL hmem' s hs hvec)

/--
---
conclusion: Lax342547.FreshKeys.fresh_keys
---
Choose the sparse exclusion uniformly for each endpoint. Project a
purported joint dependence modulo a table space onto that endpoint's
primal block. The fresh-point theorem kills every coefficient. The table
contains full channels, but their primal projections contribute zero.
-/
theorem fresh_keys {Base Comp H N : Type} [Fintype Base] [Fintype Comp] [Fintype H]
    {b degree K R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (hK : P.rank ≤ K) (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ B : Fin 2 → Finset (Fin b → Binary),
      (∀ i, (B i).card ≤ 2 * Fintype.card Comp * K * (R + 14)) ∧
      ∀ (a : Comp × Bool) (L : Fin 2 → Finset (Fin b → Binary))
        (c : Fin 2 → (Fin b → Binary) → Binary)
        (z : Fin 2 → (Fin b → Binary) → Base → Binary),
        (∀ i, (L i).card ≤ R + 14) → (∀ i, Disjoint (L i) (B i)) →
        (∑ i : Fin 2, ∑ s ∈ L i,
          c i s • primalEmbedding i (point (selectorEval (degree := degree)) s (z i s))) ∈
            tableSpace P a →
        ∀ i s, s ∈ L i → c i s = 0 := by
  classical
  have hdim (i : Fin 2) (s : Bool) (e : Comp) :
      Module.finrank Binary (projected P i (e, s)) ≤ K :=
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (e, s))).trans
      (ProjectedPins.projected_rank P i)).trans hK
  choose B hB hfresh using fun i => fresh_points (fun s e => projected P i (e, s)) (hdim i) hdegree
  refine ⟨B, hB, ?_⟩
  intro a L c z hL hdis hmem i s hs
  apply hfresh i a.2 a.1 (L i) (c i) (z i) (hL i) (hdis i) ?_ s hs
  have hp := hmem i
  fin_cases i <;> simpa [map_sum, map_smul, TableSpaces.primalProjection_embedding,
    smul_ite, Finset.sum_ite_irrel] using hp

end Lax342547Proofs.FreshKeys
