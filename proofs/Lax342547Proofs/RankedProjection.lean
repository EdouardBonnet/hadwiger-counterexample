import Lax342547.RankedProjection
import Lax342547Proofs.ResponseMatrices

namespace Lax342547Proofs.RankedProjection

open Lax342547.RankedProjection

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.TableSpaces
open Lax342547.ProjectedPins Lax342547.ResponseMatrices
open Lax342547.ConcreteGeometry

/--
---
conclusion: Lax342547.RankedProjection.bilinear_comp_rank
---
-/
theorem bilinear_comp_rank {A B V X : Type} [AddCommGroup A] [Module Binary A]
    [AddCommGroup B] [Module Binary B] [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary B]
    (β : A →ₗ[Binary] B →ₗ[Binary] Binary)
    (f : V →ₗ[Binary] A) (g : X →ₗ[Binary] B) :
    Module.finrank Binary (LinearMap.range (β.compl₁₂ f g)) ≤
      Module.finrank Binary (LinearMap.range β) := by
  have he : β.compl₁₂ f g = (LinearMap.lcomp Binary Binary g).comp (β.comp f) := rfl
  rw [he]
  exact (Lax342547Proofs.ResponseMatrices.comp_right_rank _ _).trans
    (Lax342547Proofs.ResponseMatrices.comp_left_rank _ _)

/--
---
conclusion: Lax342547.RankedProjection.matrix_bilinear_rank
---
-/
theorem matrix_bilinear_rank {B : Type} [Fintype B] (M : Matrix B B Binary) :
    by
      classical
      exact Module.finrank Binary (LinearMap.range (Matrix.toBilin' M)) ≤ M.rank := by
  classical
  have he : Matrix.toBilin' M = (dotProductBilin Binary Binary).comp M.transpose.mulVecLin := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    rw [Matrix.toBilin'_apply']
    change dotProduct v (M.mulVec w) = dotProduct (M.transpose.mulVec v) w
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  rw [he]
  exact (Lax342547Proofs.ResponseMatrices.comp_right_rank _ _).trans_eq (Matrix.rank_transpose M)

/--
---
conclusion: Lax342547.RankedProjection.linear_add_rank
---
-/
theorem linear_add_rank {V X : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (f g : V →ₗ[Binary] X) :
    Module.finrank Binary (LinearMap.range (f + g)) ≤
      Module.finrank Binary (LinearMap.range f) + Module.finrank Binary (LinearMap.range g) := by
  have hr : LinearMap.range (f + g) ≤ LinearMap.range f ⊔ LinearMap.range g := by
    rintro _ ⟨v, rfl⟩
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨v, rfl⟩) (Submodule.mem_sup_right ⟨v, rfl⟩)
  exact (Submodule.finrank_mono hr).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

/--
---
conclusion: Lax342547.RankedProjection.linear_sum_rank
---
-/
theorem linear_sum_rank {I V X : Type} [Fintype I] [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (f : I → V →ₗ[Binary] X) :
    Module.finrank Binary (LinearMap.range (∑ i, f i)) ≤
      ∑ i, Module.finrank Binary (LinearMap.range (f i)) := by
  classical
  let g : (∀ i, LinearMap.range (f i)) →ₗ[Binary] X :=
    LinearMap.lsum Binary _ Binary (fun i => (LinearMap.range (f i)).subtype)
  have hr : LinearMap.range (∑ i, f i) ≤ LinearMap.range g := by
    rintro _ ⟨v, rfl⟩
    refine ⟨fun i => (f i).rangeRestrict v, ?_⟩
    simp only [g, LinearMap.lsum_apply, Submodule.subtype_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.sum_apply]
    rfl
  exact (Submodule.finrank_mono hr).trans (by
    simpa only [Module.finrank_pi_fintype] using g.finrank_range_le)

/--
---
conclusion: Lax342547.RankedProjection.projected_endpoint_response
---
-/
theorem projected_endpoint_response {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H)) (i : Fin 2) (M A C : Matrix B B Binary)
    (hD : D.map (primalProjection i) ≤ LinearMap.ker A.mulVecLin)
    (hE : E.map (primalProjection i) ≤ LinearMap.ker C.mulVecLin) :
    ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = (matrixPair (A.transpose * M * C)).comp (LinearMap.proj i) ∧
      Module.finrank Binary (LinearMap.range β) ≤ M.rank := by
  classical
  have hDker : D ≤ LinearMap.ker (A.mulVecLin.comp (primalProjection (H := H) i)) := by
    intro v hv
    exact hD ⟨v, hv, rfl⟩
  have hEker : E ≤ LinearMap.ker (C.mulVecLin.comp (primalProjection (H := H) i)) := by
    intro v hv
    exact hE ⟨v, hv, rfl⟩
  let f := D.liftQ (A.mulVecLin.comp (primalProjection i)) hDker
  let g := E.liftQ (C.mulVecLin.comp (primalProjection i)) hEker
  let γ := Matrix.toBilin' M
  let β := γ.compl₁₂ f g
  refine ⟨β, ?_, (bilinear_comp_rank γ f g).trans (matrix_bilinear_rank M)⟩
  have hproj (j : Fin 2) (v : B → Binary) :
      primalProjection (H := H) i (primalEmbedding j v) = if j = i then v else 0 := by
    ext b
    simp [primalProjection, primalEmbedding, eq_comm]
    split_ifs <;> rfl
  have hb (j : Fin 2) :
      β.compl₁₂ (D.mkQ.comp (primalEmbedding j)) (E.mkQ.comp (primalEmbedding j)) =
        if j = i then γ.compl₁₂ A.mulVecLin C.mulVecLin else 0 := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change γ (A.mulVecLin (primalProjection i (primalEmbedding j v)))
      (C.mulVecLin (primalProjection i (primalEmbedding j w))) = _
    rw [hproj, hproj]
    by_cases hj : j = i <;> simp [hj]
  have hm : LinearMap.BilinForm.toMatrix' (γ.compl₁₂ A.mulVecLin C.mulVecLin) =
      A.transpose * M * C := by
    change LinearMap.BilinForm.toMatrix' (γ.comp A.mulVecLin C.mulVecLin) = _
    rw [LinearMap.BilinForm.toMatrix'_comp]
    simp [γ, ← Matrix.toLin'_apply']
  simp only [pureResponse, hb]
  rw [Finset.sum_eq_single i]
  · simp [hm]
  · intro j _ hji
    simp [hji, matrixPair]
  · simp

/--
---
conclusion: Lax342547.RankedProjection.projected_paired_response
---
-/
theorem projected_paired_response {B H : Type} [Fintype B] [Fintype H]
    (D E : Submodule Binary (Nominal B H)) (M A C : Fin 2 → Matrix B B Binary)
    (hD : ∀ i, D.map (primalProjection i) ≤ LinearMap.ker (A i).mulVecLin)
    (hE : ∀ i, E.map (primalProjection i) ≤ LinearMap.ker (C i).mulVecLin) :
    ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = ∑ i, (matrixPair ((A i).transpose * M i * C i)).comp (LinearMap.proj i) ∧
      Module.finrank Binary (LinearMap.range β) ≤ ∑ i, (M i).rank := by
  classical
  have he : ∀ i, ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = (matrixPair ((A i).transpose * M i * C i)).comp (LinearMap.proj i) ∧
        Module.finrank Binary (LinearMap.range β) ≤ (M i).rank := by
    intro i
    exact projected_endpoint_response D E i (M i) (A i) (C i) (hD i) (hE i)
  choose β hβ hrβ using he
  let L : ((Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary) →ₗ[Binary]
      Module.Dual Binary (Fin 2 → Matrix B B Binary) :=
    { toFun := pureResponse D E
      map_add' := Lax342547Proofs.ResponseSolvability.pure_add D E
      map_smul' := Lax342547Proofs.ResponseSolvability.pure_smul D E }
  refine ⟨∑ i, β i, ?_, (linear_sum_rank β).trans (Finset.sum_le_sum (fun i _ => hrβ i))⟩
  change L (∑ i, β i) = _
  rw [map_sum]
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hβ]

open Lax342547.TagGeometry Lax342547.ConcreteCut Lax342547.PairedWitnesses Lax342547.CutProfiles
open Lax342547.ExactPins Lax342547.BarredSpaces

/--
---
conclusion: Lax342547.RankedProjection.actual_pure_projection
---
-/
theorem actual_pure_projection {k n b degree r K : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (U V : Fin 2 → Submodule Binary (H → Binary))
    (e : Component (Tag k)) (M : Fin 2 → Moment k n b degree) :
    ∃ (A C : Fin 2 → Moment k n b degree)
      (β : (Nominal (Coordinate k n b degree) H ⧸ barred W P U (e, true)) →ₗ[Binary]
        (Nominal (Coordinate k n b degree) H ⧸ barred W P V (e, false)) →ₗ[Binary] Binary),
      pureResponse (barred W P U (e, true)) (barred W P V (e, false)) β =
        ∑ i, (matrixPair ((A i).transpose * M i * C i)).comp (LinearMap.proj i) ∧
      Module.finrank Binary (LinearMap.range β) ≤ ∑ i, (M i).rank ∧
      ∀ i, (M i - (A i).transpose * M i * C i).rank ≤ 2 * K + 28 ∧
        ((A i).transpose * M i * C i).rank ≤ (M i).rank := by
  classical
  have hAp : ∀ i, ∃ A : Moment k n b degree,
      projected P i (e, true) ⊔ individualKeys W i e ≤ LinearMap.ker A.mulVecLin ∧
      (1 - A).rank ≤ Module.finrank Binary ↥(projected P i (e, true) ⊔ individualKeys W i e) := by
    intro i
    exact Lax342547Proofs.ResponseMatrices.quotient_projection _
  have hCp : ∀ i, ∃ C : Moment k n b degree,
      projected P i (e, false) ⊔ individualKeys W i e ≤ LinearMap.ker C.mulVecLin ∧
      (1 - C).rank ≤ Module.finrank Binary ↥(projected P i (e, false) ⊔ individualKeys W i e) := by
    intro i
    exact Lax342547Proofs.ResponseMatrices.quotient_projection _
  choose A hA hrA using hAp
  choose C hC hrC using hCp
  have hD : ∀ i, (barred W P U (e, true)).map (primalProjection i) ≤ LinearMap.ker (A i).mulVecLin := by
    intro i
    exact (Lax342547Proofs.BarredSpaces.barred_projection W P U (e, true) i).trans (hA i)
  have hE : ∀ i, (barred W P V (e, false)).map (primalProjection i) ≤ LinearMap.ker (C i).mulVecLin := by
    intro i
    exact (Lax342547Proofs.BarredSpaces.barred_projection W P V (e, false) i).trans (hC i)
  obtain ⟨β, hβ, hrβ⟩ := projected_paired_response _ _ M A C hD hE
  refine ⟨A, C, β, hβ, hrβ, ?_⟩
  intro i
  constructor
  · have ha := (hrA i).trans (Lax342547Proofs.ResponseMatrices.projected_pin_key_dimension W P hK i (e, true))
    have hc := (hrC i).trans (Lax342547Proofs.ResponseMatrices.projected_pin_key_dimension W P hK i (e, false))
    have hh := (Lax342547Proofs.ResponseMatrices.projection_difference_rank (A i) (M i) (C i)).trans (Nat.add_le_add ha hc)
    omega
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end Lax342547Proofs.RankedProjection
