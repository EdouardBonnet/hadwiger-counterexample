import Lax342547.ConstrainedCompression
import Lax342547.BaseCompression
import Lax342547.ResponseMatrices

namespace Lax342547Proofs.ConstrainedCompression

open Lax342547.ConstrainedCompression

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.BaseCompression

/--
---
conclusion: Lax342547.ConstrainedCompression.vector_decomposition
---
-/
theorem vector_decomposition {k n b degree : ℕ} (v : Vector k n b degree) :
    v = constantPart v + ∑ s, ∑ q, blockEmbed s q (blockSlice s q v) := by
  classical
  ext ⟨a, c⟩
  cases c with
  | none => simp [constantPart, blockEmbed, Finset.sum_apply]
  | some c =>
    rcases c with ⟨⟨d, t⟩, j⟩ | ⟨q', j⟩ <;>
      simp [constantPart, blockEmbed, blockSlice, baseAt, Finset.sum_apply,
        Finset.sum_ite_irrel, eq_comm]

/--
---
conclusion: Lax342547.ConstrainedCompression.lifted_decomposition
---
-/
theorem lifted_decomposition {k n b degree : ℕ}
    (A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary)) (v : Vector k n b degree) :
    liftBase (blockMap A) v = constantPart v + ∑ s, ∑ q, blockEmbed s q (A q (blockSlice s q v)) := by
  classical
  ext ⟨a, c⟩
  cases c with
  | none => simp [constantPart, blockEmbed, liftBase, Finset.sum_apply]
  | some c =>
    rcases c with ⟨⟨d, t⟩, j⟩ | ⟨q', j⟩ <;>
      simp [constantPart, blockEmbed, blockSlice, baseAt, liftBase, blockMap,
        Finset.sum_apply, Finset.sum_ite_irrel, eq_comm]

/--
---
conclusion: Lax342547.ConstrainedCompression.pi_range_rank
---
-/
theorem pi_range_rank {I V X : Type} [Fintype I] [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary V] [FiniteDimensional Binary X]
    (L : I → V →ₗ[Binary] X) :
    Module.finrank Binary (LinearMap.range (LinearMap.pi L)) ≤
      ∑ i, Module.finrank Binary (LinearMap.range (L i)) := by
  let g : (∀ i, LinearMap.range (L i)) →ₗ[Binary] (I → X) :=
    { toFun := fun w i => (w i).val
      map_add' := by intro w v; rfl
      map_smul' := by intro c w; rfl }
  have hr : LinearMap.range (LinearMap.pi L) ≤ LinearMap.range g := by
    rintro _ ⟨v, rfl⟩
    exact ⟨fun i => (L i).rangeRestrict v, rfl⟩
  exact (Submodule.finrank_mono hr).trans (by
    simpa only [Module.finrank_pi_fintype] using g.finrank_range_le)

/--
---
conclusion: Lax342547.ConstrainedCompression.fixedSlices_mem
---
-/
theorem fixedSlices_mem {I : Type} [Fintype I] {k n b degree : ℕ}
    (S : I → Submodule Binary (Vector k n b degree)) (q : Block k)
    (i : I) (s : SelectorCoordinates b degree) (v : Vector k n b degree) (hv : v ∈ S i) :
    blockSlice s q v ∈ LinearMap.range (fixedSlices S q) := by
  classical
  refine ⟨Pi.single (i, s) ⟨v, hv⟩, ?_⟩
  rw [fixedSlices, LinearMap.lsum_piSingle]
  rfl

/--
---
conclusion: Lax342547.ConstrainedCompression.fixedSlices_rank
---
-/
theorem fixedSlices_rank {I : Type} [Fintype I] {k n b degree B : ℕ}
    (S : I → Submodule Binary (Vector k n b degree))
    (hS : ∀ i, Module.finrank Binary (S i) ≤ B) (q : Block k) :
    Module.finrank Binary (LinearMap.range (fixedSlices S q)) ≤
      Fintype.card I * Fintype.card (SelectorCoordinates b degree) * B := by
  have h := (fixedSlices S q).finrank_range_le
  rw [Module.finrank_pi_fintype] at h
  have hh := h.trans (Finset.sum_le_sum (fun j _ => hS j.1))
  simpa [Fintype.card_prod, mul_assoc] using hh

/--
---
conclusion: Lax342547.ConstrainedCompression.observations_rank
---
-/
theorem observations_rank {I X : Type} [Fintype I] [AddCommGroup X] [Module Binary X]
    [FiniteDimensional Binary X] {k n b degree R : ℕ}
    (T : I → Vector k n b degree →ₗ[Binary] X)
    (hT : ∀ i, Module.finrank Binary (LinearMap.range (T i)) ≤ R) (q : Block k) :
    Module.finrank Binary (LinearMap.range (observations T q)) ≤
      Fintype.card I * Fintype.card (SelectorCoordinates b degree) * R := by
  have h := Lax342547.ConstrainedCompression.pi_range_rank (fun j : I × SelectorCoordinates b degree => (T j.1).comp (blockEmbed j.2 q))
  have hle : ∀ j : I × SelectorCoordinates b degree,
      Module.finrank Binary (LinearMap.range ((T j.1).comp (blockEmbed j.2 q))) ≤ R := by
    intro j
    exact (Lax342547.ResponseMatrices.comp_left_rank _ _).trans (hT j.1)
  have hh := h.trans (Finset.sum_le_sum (fun j _ => hle j))
  simpa [observations, Fintype.card_prod, mul_assoc] using hh

/--
---
conclusion: Lax342547.ConstrainedCompression.exists_block_compression
---
-/
theorem exists_block_compression {I X : Type} [Fintype I] [AddCommGroup X] [Module Binary X]
    [FiniteDimensional Binary X] {k n b degree B R : ℕ}
    (S : I → Submodule Binary (Vector k n b degree))
    (hS : ∀ i, Module.finrank Binary (S i) ≤ B)
    (T : I → Vector k n b degree →ₗ[Binary] X)
    (hT : ∀ i, Module.finrank Binary (LinearMap.range (T i)) ≤ R) :
    ∃ A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary),
      (∀ q, Module.finrank Binary (LinearMap.range (A q)) ≤
        Fintype.card I * Fintype.card (SelectorCoordinates b degree) * (B + R)) ∧
      (∀ i v, v ∈ S i → liftBase (blockMap A) v = v) ∧
      ∀ i, (T i).comp (liftBase (blockMap A)) = T i := by
  classical
  have h : ∀ q : Block k, ∃ p : (Fin n → Binary) →ₗ[Binary] (Fin n → Binary),
      (∀ v ∈ LinearMap.range (fixedSlices S q), p v = v) ∧
      (observations T q).comp p = observations T q ∧
      Module.finrank Binary (LinearMap.range p) ≤
        Fintype.card I * Fintype.card (SelectorCoordinates b degree) * (B + R) := by
    intro q
    obtain ⟨p, hfix, hobs, hr⟩ := Lax342547.BaseCompression.fixing_observed_projection
      (LinearMap.range (fixedSlices S q)) (observations T q)
    refine ⟨p, hfix, hobs, ?_⟩
    have hh := hr.trans (Nat.add_le_add (Lax342547.ConstrainedCompression.fixedSlices_rank S hS q) (Lax342547.ConstrainedCompression.observations_rank T hT q))
    simpa only [Nat.mul_add] using hh
  choose A hfix hobs hr using h
  refine ⟨A, hr, ?_, ?_⟩
  · intro i v hv
    have hh (s : SelectorCoordinates b degree) (q : Block k) :
        A q (blockSlice s q v) = blockSlice s q v :=
      hfix q _ (Lax342547.ConstrainedCompression.fixedSlices_mem S q i s v hv)
    ext ⟨s, c⟩
    cases c with
    | none => rfl
    | some c =>
      rcases c with ⟨⟨d, t⟩, j⟩ | ⟨q, j⟩
      · exact congrFun (hh s (Sum.inl (d, t))) j
      · exact congrFun (hh s (Sum.inr q)) j
  · intro i
    apply LinearMap.ext
    intro v
    have hb (s : SelectorCoordinates b degree) (q : Block k) (w : Fin n → Binary) :
        T i (blockEmbed s q (A q w)) = T i (blockEmbed s q w) :=
      congrFun (DFunLike.congr_fun (hobs q) w) (i, s)
    change T i (liftBase (blockMap A) v) = T i v
    calc
      _ = T i (constantPart v) + ∑ s, ∑ q, T i (blockEmbed s q (A q (blockSlice s q v))) := by
        rw [Lax342547.ConstrainedCompression.lifted_decomposition]
        simp only [map_add, map_sum]
      _ = T i (constantPart v) + ∑ s, ∑ q, T i (blockEmbed s q (blockSlice s q v)) := by
        simp only [hb]
      _ = T i v := by
        conv_rhs => rw [Lax342547.ConstrainedCompression.vector_decomposition v]
        simp only [map_add, map_sum]

open Lax342547.PairedWitnesses Lax342547.TableSpaces Lax342547.ProjectedPins
open Lax342547.ConcreteCut Lax342547.ResponseMatrices
open Lax342547.CutProfiles Lax342547.ExactPins Lax342547.BarredSpaces

/--
---
conclusion: Lax342547.ConstrainedCompression.preserved_matrix
---
-/
theorem preserved_matrix {B : Type} [Fintype B]
    (f : (B → Binary) →ₗ[Binary] (B → Binary)) (M : Matrix B B Binary)
    (hrow : M.mulVecLin.comp f = M.mulVecLin)
    (hcol : M.transpose.mulVecLin.comp f = M.transpose.mulVecLin) : by
      classical
      exact (LinearMap.toMatrix' f).transpose * M * LinearMap.toMatrix' f = M := by
  classical
  have hr := congrArg LinearMap.toMatrix' hrow
  have hc := congrArg LinearMap.toMatrix' hcol
  simp only [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at hr hc
  have ht := congrArg Matrix.transpose hc
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at ht
  rw [ht, hr]

/--
---
conclusion: Lax342547.ConstrainedCompression.actual_block_compression
---
-/
theorem actual_block_compression {k n b degree r K R : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (i : Fin 2) (M : Component (Tag k) → Moment k n b degree)
    (hM : ∀ e, (M e).rank ≤ R) :
    ∃ A : Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary),
      (∀ q, Module.finrank Binary (LinearMap.range (A q)) ≤
        2 * Fintype.card (SelectorCoordinates b degree) * Fintype.card (Component (Tag k)) *
          (K + 14 + R)) ∧
      (∀ a v, v ∈ projected P i a ⊔ individualKeys W i a.1 → liftBase (blockMap A) v = v) ∧
      ∀ e, by
        classical
        exact
        (LinearMap.toMatrix' (liftBase (Coord := SelectorCoordinates b degree) (blockMap A))).transpose *
          M e * LinearMap.toMatrix' (liftBase (blockMap A)) = M e := by
  classical
  let S (a : Component (Tag k) × Bool) := projected P i a ⊔ individualKeys W i a.1
  let T (a : Component (Tag k) × Bool) : Vector k n b degree →ₗ[Binary] Vector k n b degree :=
    if a.2 then (M a.1).mulVecLin else (M a.1).transpose.mulVecLin
  have hS : ∀ a, Module.finrank Binary (S a) ≤ K + 14 :=
    fun a => Lax342547.ResponseMatrices.projected_pin_key_dimension W P hK i a
  have hT : ∀ a, Module.finrank Binary (LinearMap.range (T a)) ≤ R := by
    rintro ⟨e, c⟩
    cases c
    · change (M e).transpose.rank ≤ R
      simpa only [Matrix.rank_transpose] using hM e
    · exact hM e
  obtain ⟨A, hr, hfix, hobs⟩ := Lax342547.ConstrainedCompression.exists_block_compression S hS T hT
  refine ⟨A, ?_, hfix, ?_⟩
  · intro q
    simpa [Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc] using hr q
  · intro e
    exact Lax342547.ConstrainedCompression.preserved_matrix _ _ (by simpa [T] using hobs (e, true))
      (by simpa [T] using hobs (e, false))

end Lax342547Proofs.ConstrainedCompression
