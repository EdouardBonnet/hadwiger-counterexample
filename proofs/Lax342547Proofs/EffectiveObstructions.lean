import Lax342547.EffectiveObstructions
import Lax342547Proofs.DerivativeResponses
import Lax342547Proofs.PrimalRetractions
import Lax342547Proofs.EffectiveBounds

namespace Lax342547Proofs.EffectiveObstructions

open Lax342547.MomentSpace Lax342547.ProjectedPins Lax342547.PrimalContractions
open Lax342547.TensorAnnihilators

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.EffectiveObstructions.rows_of_contraction_zero
---
Every functional annihilating the proposed row space kills each row,
because the corresponding matrix contraction is zero. Coordinate duality
and double annihilation give membership in the proposed row space.
-/
theorem rows_of_contraction_zero {B : Type} [Fintype B]
    (M : Matrix B B Binary) (T : Submodule Binary (B → Binary))
    (h : ∀ ψ : Module.Dual Binary (B → Binary), T ≤ LinearMap.ker ψ →
      M.mulVecLin (coordinates ψ) = 0) : ∀ i, (fun j => M i j) ∈ T := by
  classical
  intro i
  rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := T)]
  apply (Submodule.mem_dualCoannihilator _).mpr
  intro ψ hψ
  have hk : T ≤ LinearMap.ker ψ := by
    intro v hv
    exact (Submodule.mem_dualAnnihilator ψ).mp hψ v hv
  have hz := congrFun (h ψ hk) i
  rw [Lax342547Proofs.TensorAnnihilators.functional_coordinates]
  change (∑ j, M i j * dualCoordinates ψ j) = 0 at hz
  exact hz

theorem map_coordinates {B : Type} [Fintype B] [DecidableEq B]
    (p : (B → Binary) →ₗ[Binary] (B → Binary)) (v : B → Binary) (a : B) :
    (∑ i, v i * p (Pi.single i 1) a) = p v a := by
  have he := congrArg p (pi_eq_sum_univ' v)
  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    (congrFun he a).symm

/--
---
conclusion: Lax342547.EffectiveObstructions.tensor_of_columns_rows
---
Choose linear retractions onto both factor spaces. Their images of
coordinate basis vectors lie in the two factors. The row and column
conditions reconstruct the matrix as a finite sum of those outer products.
-/
theorem tensor_of_columns_rows {B : Type} [Fintype B]
    (M : Matrix B B Binary) (S T : Submodule Binary (B → Binary))
    (hcol : ∀ j, (fun i => M i j) ∈ S) (hrow : ∀ i, (fun j => M i j) ∈ T) :
    M ∈ tensorSpace S T := by
  classical
  obtain ⟨p, hp, hfixp, _⟩ := Lax342547Proofs.PrimalRetractions.preserving_retraction S ⊤ (by simp)
  obtain ⟨q, hq, hfixq, _⟩ := Lax342547Proofs.PrimalRetractions.preserving_retraction T ⊤ (by simp)
  let A := fun i => p (Pi.single i 1)
  let Bv := fun j => q (Pi.single j 1)
  let Z := ∑ i, ∑ j, M i j • Matrix.vecMulVec (A i) (Bv j)
  have hZ : Z ∈ tensorSpace S T := by
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨A i, hp _, Bv j, hq _, rfl⟩
  have he : Z = M := by
    ext a b
    simp only [Z, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    calc
      _ = ∑ i, A i a * (∑ j, M i j * Bv j b) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, A i a * M i b := by
        apply Finset.sum_congr rfl
        intro i _
        have hr := map_coordinates q (fun j => M i j) b
        rw [hfixq _ (hrow i)] at hr
        exact congrArg (A i a * ·) hr
      _ = M a b := by
        have hc := map_coordinates p (fun i => M i b) a
        rw [hfixp _ (hcol b)] at hc
        simpa only [A, mul_comm] using hc
  exact he ▸ hZ

open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut
open Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.ExactPins Lax342547.PinLabelExclusions
open Lax342547.SparsePins Lax342547.BarredSpaces Lax342547.ResidualLabels

/--
---
conclusion: Lax342547.EffectiveObstructions.unselected_vector
---
Decompose the sparse vector into a projected pin and an individual key
vector. Fresh coefficient extraction makes the entire key vector zero.
-/
theorem unselected_vector {k n b degree r R : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (a : Component (Tag k) × Bool) (L : Finset (Fin b → Binary))
    (hL : L.card ≤ R) (v : (Fin b → Binary) → Option (Base k n) → Binary)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (hfresh : ∀ z t, (W.left i z t).label ∉ A i)
    (h : (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) ∈
      projected P i a ⊔ individualKeys W i a.1) :
    (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) ∈ projected P i a := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp h
  have hpin : (∑ s ∈ L, labelTensor (selectorEval (degree := degree)) s (v s)) - q ∈ projected P i a := by
    rw [← hpq, add_sub_cancel_right]
    exact hp
  have hqzero := Lax342547Proofs.BarredElimination.individual_keys_zero W P A hA i a L hL v
    hdisjoint hfresh q hq hpin
  rw [hqzero, add_zero] at hpq
  exact hpq ▸ hp

/--
---
conclusion: Lax342547.EffectiveObstructions.sparse_columns
---
Each column of a separated label block keeps its selector row factor.
Reading that column supplies explicit base coefficients on the same labels.
-/
theorem sparse_columns {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    (p : Label → Coord → Binary) (L : Finset Label)
    (Z : Label → Matrix Base Base Binary) (j : Coord × Base) :
    ∃ v : Label → Base → Binary,
      (fun a => (∑ s ∈ L, Lax342547.TensorBlocks.block p s (Z s)) a j) =
        ∑ s ∈ L, labelTensor p s (v s) := by
  classical
  refine ⟨fun s a => p s j.1 * Z s a j.2, ?_⟩
  ext ⟨q, a⟩
  simp [Lax342547.TensorBlocks.block, labelTensor, Matrix.sum_apply, mul_assoc]

/--
---
conclusion: Lax342547.EffectiveObstructions.transpose_blocks
---
Transposition preserves the selector factors and transposes the base
block. Commutativity exchanges the two selector scalar factors.
-/
theorem transpose_blocks {Label Coord Base : Type}
    (p : Label → Coord → Binary) (L : Finset Label)
    (Z : Label → Matrix Base Base Binary) :
    (∑ s ∈ L, Lax342547.TensorBlocks.block p s (Z s)).transpose =
      ∑ s ∈ L, Lax342547.TensorBlocks.block p s ((Z s).transpose) := by
  classical
  ext a b
  simp [Matrix.sum_apply, Matrix.transpose_apply, Lax342547.TensorBlocks.block, mul_comm]

/--
---
conclusion: Lax342547.EffectiveObstructions.unselected_tensor
---
Apply sparse key elimination to every column and to the columns of the
transposed matrix. Actual projected pin row/column membership then gives
tensor membership in the two projected pin factors.
-/
theorem unselected_tensor {k n b degree r R : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (i : Fin 2) (e : Component (Tag k)) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (hfresh : ∀ z t, (W.left i z t).label ∉ A i)
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (M : Moment k n b degree) (hM : M = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (hcol : ∀ j, (fun a => M a j) ∈ projected P i (e, true) ⊔ individualKeys W i e)
    (hrow : ∀ a, (fun j => M a j) ∈ projected P i (e, false) ⊔ individualKeys W i e) :
    M ∈ tensorSpace (projected P i (e, true)) (projected P i (e, false)) := by
  apply tensor_of_columns_rows
  · intro j
    obtain ⟨v, hv⟩ := sparse_columns selectorEval L Z j
    have he : (fun a => M a j) = ∑ s ∈ L, labelTensor selectorEval s (v s) := by
      rw [hM]
      exact hv
    rw [he]
    apply unselected_vector W P A hA i (e, true) L hL v hdisjoint hfresh
    rw [← he]
    exact hcol j
  · intro a
    obtain ⟨v, hv⟩ := sparse_columns selectorEval L (fun s => (Z s).transpose) a
    have ht : M.transpose = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s ((Z s).transpose) := by
      rw [hM]
      exact transpose_blocks selectorEval L Z
    have he : (fun j => M a j) = ∑ s ∈ L, labelTensor selectorEval s (v s) := by
      change (fun j => M.transpose j a) = _
      rw [ht]
      exact hv
    rw [he]
    apply unselected_vector W P A hA i (e, false) L hL v hdisjoint hfresh
    rw [← he]
    exact hrow a

open Lax342547.TableSpaces Lax342547.TableContractions Lax342547.DerivativeResponses

/--
---
conclusion: Lax342547.EffectiveObstructions.effective_component
---
The actual rank-one derivative tests and table injection flags kill both
reciprocal contractions. Double annihilation gives the pin-plus-key rows
and columns; unselected sparse support removes their key directions.
-/
theorem effective_component {k n b degree r R : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (hU : ∀ j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (L : Finset (Fin b → Binary)) (hL : L.card ≤ R) (hdisjoint : Disjoint L (chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : (x i).val e = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s)) :
    (x i).val e ∈ tensorSpace (projected P i (e, true)) (projected P i (e, false)) := by
  have hrow := rows_of_contraction_zero ((x i).val e) (projected P i (e, false) ⊔ individualKeys W i e)
    (fun ψ hψ => Lax342547Proofs.DerivativeResponses.plus_contraction_zero W P Q A hA hfresh U V T hT
      F hF z x h e i hU L hL hdisjoint Z hM ψ hψ)
  have hcol := rows_of_contraction_zero ((x i).val e).transpose
    (projected P i (e, true) ⊔ individualKeys W i e)
    (fun ψ hψ => Lax342547Proofs.DerivativeResponses.minus_contraction_zero W P Q A hA hfresh U V T hT
      F hF z x h e i hV L hL hdisjoint Z hM ψ hψ)
  exact unselected_tensor W P A hA i e L hL hdisjoint (hfresh i) Z _ hM hcol hrow

/--
---
conclusion: Lax342547.EffectiveObstructions.obstruction_decomposition
---
Subtract the selected scalar atoms supplied by the full obstruction
decomposition. The remainder retains full annihilation and bounded
unselected component supports. Every actual component is therefore in
its projected pin tensor space, so both remainder profiles are effective.
-/
theorem obstruction_decomposition {k n b degree r K : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]
    (hk : 0 < k) (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (hU : ∀ e j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (hV : ∀ e j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) :
    ∃ c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary,
      ∀ i, ((x - Lax342547.SelectedRemoval.selectedPart W c) i) ∈
        effective (Profile k n b degree) P i := by
  classical
  obtain ⟨c, L, Z, hann, hlabels⟩ := Lax342547Proofs.DerivativeResponses.unselected_obstruction hk W P Q
    hK A hA hfresh U V F z x h hdegree
  refine ⟨c, ?_⟩
  intro i e
  apply effective_component W P Q A hA hfresh U V T hT F hF z _ hann e i (hU e) (hV e)
    (L i e) (hlabels i e).1 _ (Z i e) (hlabels i e).2.2.2
  exact Finset.disjoint_left.mpr (fun s hs hchosen => ((hlabels i e).2.1 s hs).1 hchosen)

end Lax342547Proofs.EffectiveObstructions
