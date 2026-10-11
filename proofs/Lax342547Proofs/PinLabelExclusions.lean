import Lax342547.PinLabelExclusions
import Lax342547Proofs.SparsePins
import Lax342547Proofs.TableSpaces
import Lax342547.ProjectedPins

namespace Lax342547Proofs.PinLabelExclusions

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces
open Lax342547.PinLabelExclusions Lax342547.KeySpans

variable {Base Comp H N : Type} {b degree : ℕ}

/--
---
conclusion: Lax342547.PinLabelExclusions.covers_exists
---
Apply the full sparse-pin label cover independently at the two endpoints,
simultaneously over both signs and every component, retaining its exact budget.
-/
theorem covers_exists [Fintype Base] [Fintype Comp] [Fintype H] {K R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (hK : P.rank ≤ K) (hdegree : (K + 1) * (R + 14) ≤ degree + 1) :
    ∃ A : Fin 2 → Finset (Fin b → Binary),
      (∀ i, (A i).card ≤ 2 * Fintype.card Comp * K * (R + 14)) ∧ Covers P A R := by
  have hdim (i : Fin 2) (sign : Bool) (e : Comp) :
      Module.finrank Binary (projected P i (e, sign)) ≤ K :=
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (e, sign))).trans
      (Lax342547.ProjectedPins.projected_rank P i)).trans hK
  choose A hsize hcover using fun i => SparsePins.sparse_pin_labels_finset
    (fun sign e => projected P i (e, sign)) (hdim i) hdegree
  exact ⟨A, hsize, fun i a => hcover i a.2 a.1⟩

/--
---
conclusion: Lax342547.PinLabelExclusions.fresh_coefficient
---
A fresh selected label has zero coefficient in every short pin expansion,
even when its other labels meet the exclusion.
-/
theorem fresh_coefficient {R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Comp × Bool) (L : Finset (Fin b → Binary))
    (v : (Fin b → Binary) → Option Base → Binary) (hL : L.card ≤ R + 14)
    (hmem : (∑ t ∈ L, Lax342547.SparsePins.labelTensor
      (selectorEval (degree := degree)) t (v t)) ∈ projected P i a)
    (s : Fin b → Binary) (hs : s ∈ L) (hfresh : s ∉ A i) : v s = 0 := by
  by_contra hv
  exact hfresh (hA i a L v hL hmem s hs hv)

/--
---
conclusion: Lax342547.PinLabelExclusions.keys_exclusion
---
Project a table dependence onto each endpoint. Absorb each point-ray
coefficient into its affine base vector and apply the stronger cover;
the constant coordinate identifies that coefficient.
-/
theorem keys_exclusion {R : ℕ}
    (P : Pin (Comp × Bool) (Fin 2 × ((SelectorCoordinates b degree × Option Base) ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R) : Excludes P A := by
  classical
  intro a L c z hcard hfresh hmem i s hs
  have hp := hmem i
  have hp' : (∑ t ∈ L i, c i t • point (selectorEval (degree := degree)) t (z i t)) ∈
      projected P i a := by
    fin_cases i <;> simpa [map_sum, map_smul, TableSpaces.primalProjection_embedding,
      smul_ite, Finset.sum_ite_irrel] using hp
  have heq (t : Fin b → Binary) :
      Lax342547.SparsePins.labelTensor (selectorEval (degree := degree)) t
        (c i t • baseEval (z i t)) = c i t • point (selectorEval (degree := degree)) t (z i t) := by
    ext x
    simp [Lax342547.SparsePins.labelTensor, point]
  have hmem' : (∑ t ∈ L i, Lax342547.SparsePins.labelTensor
      (selectorEval (degree := degree)) t (c i t • baseEval (z i t))) ∈ projected P i a := by
    simpa only [heq] using hp'
  have hz := Lax342547.PinLabelExclusions.fresh_coefficient P A hA i a (L i) (fun t => c i t • baseEval (z i t))
    ((hcard i).trans (by omega)) hmem' s hs (Finset.disjoint_left.mp (hfresh i) hs)
  have hc := congrFun hz none
  simpa [baseEval] using hc

end Lax342547Proofs.PinLabelExclusions
