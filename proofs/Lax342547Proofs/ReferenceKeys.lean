import Lax342547.ReferenceKeys
import Lax342547Proofs.GramNormalization
import Lax342547Proofs.FiniteUniform

namespace Lax342547Proofs.ReferenceKeys
open Lax342547.ReferenceKeys

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace
open scoped ENNReal

/--
---
conclusion: Lax342547.ReferenceKeys.space_card_upper
---
-/
theorem space_card_upper {Comp N : Type} [Fintype Comp] [Fintype N]
    (Pos : Comp → Type) [∀ e, Fintype (Pos e)]
    (G : ∀ e, Matrix (Pos e) (Pos e) Binary) : by
      classical
      exact Fintype.card (space Pos N G) ≤
        2 ^ ((2 * ∑ e, Fintype.card (Pos e)) * Fintype.card N) := by
  classical
  calc
    _ ≤ Fintype.card (Tuples Comp Pos N) := Fintype.card_subtype_le _
    _ = _ := by
      have hc (e : Comp) : Fintype.card (Matrix N (Pos e) Binary) =
          2 ^ (Fintype.card N * Fintype.card (Pos e)) := by
        simp [Matrix, ZMod.card, ← pow_mul, Nat.mul_comm]
      change Fintype.card (∀ e, Matrix N (Pos e) Binary × Matrix N (Pos e) Binary) = _
      rw [Fintype.card_pi]
      simp only [Fintype.card_prod, hc, ← pow_add ]
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring

/--
---
conclusion: Lax342547.ReferenceKeys.block_reference_lower
---
-/
theorem block_reference_lower {I N : Type} [Fintype I] [Fintype N]
    [DecidableEq I] [DecidableEq N] (G : Matrix I I Binary)
    (hN : 2 * Fintype.card I + 1 ≤ Fintype.card N) :
    1 / (2 : ℝ≥0∞) ^ (Fintype.card I * Fintype.card I + 2) ≤
      ((PMF.uniformOfFintype (Matrix N I Binary × Matrix N I Binary)).map
        (fun x => x.1.transpose * x.2)) G := by
  have h := Lax342547Proofs.GramNormalization.normalization_quarter G
    (by simpa only [two_mul] using hN)
  apply le_trans h
  have hmono := (PMF.uniformOfFintype (Matrix N I Binary × Matrix N I Binary)).toOuterMeasure.mono
    (show {x | Function.Injective x.1.mulVec ∧ Function.Injective x.2.mulVec ∧ x.1.transpose * x.2 = G} ⊆
      {x | x.1.transpose * x.2 = G} from fun _ hx => hx.2.2)
  have he : ((PMF.uniformOfFintype (Matrix N I Binary × Matrix N I Binary)).map
      (fun x => x.1.transpose * x.2)) G =
      (PMF.uniformOfFintype (Matrix N I Binary × Matrix N I Binary)).toOuterMeasure
        {x | x.1.transpose * x.2 = G} := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl
  rw [he]
  exact hmono

/--
---
conclusion: Lax342547.ReferenceKeys.reference_density_lower
---
-/
theorem reference_density_lower {Comp N : Type} [Fintype Comp] [Fintype N]
    [DecidableEq Comp] [DecidableEq N]
    (Pos : Comp → Type) [∀ e, Fintype (Pos e)] [∀ e, DecidableEq (Pos e)]
    (G : ∀ e, Matrix (Pos e) (Pos e) Binary)
    (hN : ∀ e, 2 * Fintype.card (Pos e) + 1 ≤ Fintype.card N) :
    (∏ e, 1 / (2 : ℝ≥0∞) ^ (Fintype.card (Pos e) * Fintype.card (Pos e) + 2)) ≤
      (PMF.uniformOfFintype (Tuples Comp Pos N)).toOuterMeasure (space Pos N G) := by
  classical
  have he : (PMF.uniformOfFintype (Tuples Comp Pos N)).toOuterMeasure (space Pos N G) =
      ((PMF.uniformOfFintype (Tuples Comp Pos N)).map
        (fun x e => (x e).1.transpose * (x e).2)) G := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext x
    simp only [space, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
  rw [he]
  dsimp only [Tuples]
  have hm := Lax342547Proofs.FiniteUniform.map_pi_apply
    (fun e (x : Matrix N (Pos e) Binary × Matrix N (Pos e) Binary) => x.1.transpose * x.2) G
  rw [hm]
  exact Finset.prod_le_prod' (fun e _ => block_reference_lower (G e) (hN e))

end Lax342547Proofs.ReferenceKeys
