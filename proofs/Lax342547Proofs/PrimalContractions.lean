import Lax342547.PrimalContractions
import Lax342547.BarredElimination
import Lax342547.BarredSpaces
import Lax342547Proofs.TensorAnnihilators

namespace Lax342547Proofs.PrimalContractions

open Lax342547.MomentSpace Lax342547.TableSpaces Lax342547.PairedAnnihilators
open Lax342547.TensorAnnihilators
open Lax342547.ConcreteGeometry Lax342547.ProjectedPins

set_option backward.isDefEq.respectTransparency false

open Lax342547.PrimalContractions

theorem product_pair {B : Type} [Fintype B]
    (M : Matrix B B Binary) (φ ψ : Module.Dual Binary (B → Binary)) :
    by classical
       exact matrixPair (LinearMap.BilinForm.toMatrix' (φ.smulRight ψ)) M =
         φ (M.mulVecLin (coordinates ψ)) := by
  classical
  have hc := Lax342547Proofs.TensorAnnihilators.pure_rank_one M ⊥ ⊥ φ ψ bot_le bot_le
  have he : (((⊥ : Submodule Binary (B → Binary)).liftQ φ bot_le).smulRight
      ((⊥ : Submodule Binary (B → Binary)).liftQ ψ bot_le)).compl₁₂
        (⊥ : Submodule Binary (B → Binary)).mkQ (⊥ : Submodule Binary (B → Binary)).mkQ =
      φ.smulRight ψ := by
    ext v w
    rfl
  simpa only [pureContraction, he, coordinates] using hc

/--
---
conclusion: Lax342547.PrimalContractions.endpoint_vector
---
Test products of nominal quotient functionals. The tested functional
is supported on one endpoint; the other tensor vanishes. Double
annihilation places that endpoint contraction in the nominal subspace.
-/
theorem endpoint_vector {B H : Type} [Fintype B]
    (M : Fin 2 → Matrix B B Binary) (D E : Submodule Binary (Nominal B H))
    (h : PairedAnnihilates M D E) (i : Fin 2)
    (T : Submodule Binary (B → Binary)) (hE : E.map (primalProjection i) ≤ T)
    (ψ : Module.Dual Binary (B → Binary)) (hψ : T ≤ LinearMap.ker ψ) :
    primalEmbedding i ((M i).mulVecLin (coordinates ψ)) ∈ D := by
  classical
  rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := D)]
  apply (Submodule.mem_dualCoannihilator _).mpr
  intro φ hφ
  have hφker : D ≤ LinearMap.ker φ := by
    intro v hv
    exact (Submodule.mem_dualAnnihilator φ).mp hφ v hv
  let ψnom := ψ.comp (primalProjection (H := H) i)
  have hψker : E ≤ LinearMap.ker ψnom := by
    intro v hv
    exact hψ (hE ⟨v, hv, rfl⟩)
  let β := (D.liftQ φ hφker).smulRight (E.liftQ ψnom hψker)
  have hproj (j : Fin 2) (v : B → Binary) :
      primalProjection (H := H) i (primalEmbedding j v) = if j = i then v else 0 := by
    ext b
    simp [primalProjection, primalEmbedding, eq_comm]
    split_ifs <;> rfl
  have hb (j : Fin 2) :
      β.compl₁₂ (D.mkQ.comp (primalEmbedding j)) (E.mkQ.comp (primalEmbedding j)) =
        if j = i then (φ.comp (primalEmbedding i)).smulRight ψ else 0 := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change φ (primalEmbedding j v) * ψ (primalProjection i (primalEmbedding j w)) = _
    rw [hproj]
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  have hh := h β
  change (∑ j, matrixPair (LinearMap.BilinForm.toMatrix'
    (β.compl₁₂ (D.mkQ.comp (primalEmbedding j))
      (E.mkQ.comp (primalEmbedding j)))) (M j)) = 0 at hh
  simp only [hb] at hh
  have htest : matrixPair (LinearMap.BilinForm.toMatrix'
      ((φ.comp (primalEmbedding i)).smulRight ψ)) (M i) = 0 := by
    fin_cases i <;> simpa [matrixPair] using hh
  rw [product_pair] at htest
  exact htest

/--
---
conclusion: Lax342547.PrimalContractions.sparse_contraction
---
Expand the matrix contraction entrywise and interchange the finite sums.
Each label keeps its selector row factor, with a new base coefficient.
-/
theorem sparse_contraction {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    (p : Label → Coord → Binary) (L : Finset Label)
    (Z : Label → Matrix Base Base Binary)
    (v : Coord × Base → Binary) :
    (∑ s ∈ L, Lax342547.TensorBlocks.block p s (Z s)).mulVecLin v =
      ∑ s ∈ L, Lax342547.SparsePins.labelTensor p s
        (fun a => ∑ c, p s c.1 * Z s a c.2 * v c) := by
  classical
  ext ⟨q, a⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Lax342547.TensorBlocks.block, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_mul, Finset.sum_apply, Lax342547.SparsePins.labelTensor]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

open Lax342547.TagGeometry Lax342547.ConcreteCut Lax342547.CutProfiles
open Lax342547.PairedWitnesses Lax342547.ExactPins Lax342547.SparsePins
open Lax342547.PinLabelExclusions Lax342547.BarredSpaces Lax342547.ResidualLabels

/--
---
conclusion: Lax342547.PrimalContractions.unselected_pin_contraction
---
The generic quotient test puts the individual contraction in the actual
barred space. Its own endpoint has the given unselected sparse support,
and the other endpoint is zero. Strong exclusion and protected/private
complementarity therefore put it in the actual pinned primal subspace.
-/
theorem unselected_pin_contraction {k n b degree r R : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Fin 2 → Submodule Binary (H → Binary)) (e : Component (Tag k))
    (hU : ∀ j, IsCompl (protectedChannel P j (e, true)) (U j))
    (M : Fin 2 → Moment k n b degree)
    (h : PairedAnnihilates M (barred W P U (e, true)) (barred W P V (e, false)))
    (i : Fin 2) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : M i = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : projected P i (e, false) ⊔ individualKeys W i e ≤ LinearMap.ker ψ) :
    (M i).mulVecLin (coordinates ψ) ∈ pinnedPrimal P i (e, true) := by
  classical
  have hd := Lax342547.PrimalContractions.endpoint_vector M _ _ h i _
    (Lax342547.BarredSpaces.barred_projection W P V (e, false) i) ψ hψ
  let coeff := fun s a => ∑ c, selectorEval (degree := degree) s c.1 * Z s a c.2 * coordinates ψ c
  have hsparse : (M i).mulVecLin (coordinates ψ) = ∑ s ∈ L, labelTensor selectorEval s (coeff s) := by
    rw [hM]
    exact Lax342547.PrimalContractions.sparse_contraction _ L Z _
  refine Lax342547.BarredElimination.sparse_barred W P A hA hfresh U (e, true) hU
    (fun j => if j = i then L else ∅) ?_ ?_ (fun _ => coeff) _ ?_ ?_ hd
  · intro j
    by_cases hj : j = i <;> simp [hj, hL]
  · intro j
    by_cases hj : j = i
    · subst j
      simpa using hdisjoint
    · simp [hj]
  · intro j a
    simp [primalEmbedding]
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [primalProjection, primalEmbedding] using hsparse
    · have hz : primalProjection j (primalEmbedding (H := H) i
          ((M i).mulVecLin (coordinates ψ))) = 0 := by
        ext c
        simp [primalProjection, primalEmbedding, hj]
      simpa [hj] using hz

/--
---
conclusion: Lax342547.PrimalContractions.unselected_pin_contraction_mode
---
The sparse contraction argument works in either sign. The quotient
test places it in the indicated barred space; sparse key elimination
and the same-sign protected/private complement put it in the actual pin.
-/
theorem unselected_pin_contraction_mode {k n b degree r R : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary)) (hA : Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (p : Bool) (U V : Fin 2 → Submodule Binary (H → Binary)) (e : Component (Tag k))
    (hU : ∀ j, IsCompl (protectedChannel P j (e, p)) (U j))
    (M : Fin 2 → Moment k n b degree)
    (h : PairedAnnihilates M (barred W P U (e, p)) (barred W P V (e, !p)))
    (i : Fin 2) (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : M i = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : projected P i (e, !p) ⊔ individualKeys W i e ≤ LinearMap.ker ψ) :
    (M i).mulVecLin (coordinates ψ) ∈ pinnedPrimal P i (e, p) := by
  classical
  have hd := Lax342547.PrimalContractions.endpoint_vector M _ _ h i _
    (Lax342547.BarredSpaces.barred_projection W P V (e, !p) i) ψ hψ
  let coeff := fun s a => ∑ c, selectorEval (degree := degree) s c.1 * Z s a c.2 * coordinates ψ c
  have hsparse : (M i).mulVecLin (coordinates ψ) = ∑ s ∈ L, labelTensor selectorEval s (coeff s) := by
    rw [hM]
    exact Lax342547.PrimalContractions.sparse_contraction _ L Z _
  refine Lax342547.BarredElimination.sparse_barred W P A hA hfresh U (e, p) hU
    (fun j => if j = i then L else ∅) ?_ ?_ (fun _ => coeff) _ ?_ ?_ hd
  · intro j
    by_cases hj : j = i <;> simp [hj, hL]
  · intro j
    by_cases hj : j = i
    · subst j
      simpa using hdisjoint
    · simp [hj]
  · intro j a
    simp [primalEmbedding]
  · intro j
    by_cases hj : j = i
    · subst j
      simpa [primalProjection, primalEmbedding] using hsparse
    · have hz : primalProjection j (primalEmbedding (H := H) i
          ((M i).mulVecLin (coordinates ψ))) = 0 := by
        ext c
        simp [primalProjection, primalEmbedding, hj]
      simpa [hj] using hz

end Lax342547Proofs.PrimalContractions
