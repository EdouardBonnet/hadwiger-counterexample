import Lax342547.ResponseMatrices
import Mathlib.LinearAlgebra.Matrix.Rank
import Lax342547Proofs.MomentRecovery
import Lax342547.BarredSpaces
import Lax342547.ProjectedPins
import Lax342547Proofs.PrimalRetractions
import Lax342547Proofs.ResponseSolvability

namespace Lax342547Proofs.ResponseMatrices

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.ConcreteGeometry
open Lax342547.TensorContractions Lax342547.ResponseMatrices

/--
---
conclusion: Lax342547.ResponseMatrices.coefficients_product
---
-/
theorem coefficients_product {B H : Type} [Fintype B] [Fintype H]
    (f g : (B → Binary) →ₗ[Binary] (H → Binary)) : by
      classical
      exact coefficients f g = (LinearMap.toMatrix' f).transpose * LinearMap.toMatrix' g := by
  classical
  ext i j
  simp [coefficients, LinearMap.BilinForm.toMatrix'_apply,
    LinearMap.toMatrix'_apply, Matrix.mul_apply, dotProduct]

/--
---
conclusion: Lax342547.ResponseMatrices.toMatrix_rank
---
-/
theorem toMatrix_rank {B H : Type} [Fintype B] [Fintype H]
    (f : (B → Binary) →ₗ[Binary] (H → Binary)) : by
      classical
      exact (LinearMap.toMatrix' f).rank = Module.finrank Binary (LinearMap.range f) := by
  classical
  have he : (LinearMap.toMatrix' f).mulVecLin = f := by
    apply LinearMap.ext
    intro v
    funext h
    exact congrFun (LinearMap.toMatrix'_mulVec f v) h
  change Module.finrank Binary (LinearMap.range (LinearMap.toMatrix' f).mulVecLin) = _
  rw [he]

/--
---
conclusion: Lax342547.ResponseMatrices.coefficients_rank
---
-/
theorem coefficients_rank {B H : Type} [Fintype B] [Fintype H]
    (f g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    (coefficients f g).rank ≤ min (Module.finrank Binary (LinearMap.range f))
      (Module.finrank Binary (LinearMap.range g)) := by
  classical
  rw [Lax342547.ResponseMatrices.coefficients_product]
  have hr := Matrix.rank_mul_le (LinearMap.toMatrix' f).transpose (LinearMap.toMatrix' g)
  simpa only [Matrix.rank_transpose, Lax342547.ResponseMatrices.toMatrix_rank] using hr

/--
---
conclusion: Lax342547.ResponseMatrices.projection_difference
---
-/
theorem projection_difference {B : Type} [Fintype B] [DecidableEq B]
    (A M C : Matrix B B Binary) :
    M - A.transpose * M * C = (1 - A).transpose * M + A.transpose * M * (1 - C) := by
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one]
  abel

/--
---
conclusion: Lax342547.ResponseMatrices.projection_difference_rank
---
-/
theorem projection_difference_rank {B : Type} [Fintype B] [DecidableEq B]
    (A M C : Matrix B B Binary) :
    (M - A.transpose * M * C).rank ≤ (1 - A).rank + (1 - C).rank := by
  rw [Lax342547.ResponseMatrices.projection_difference]
  apply (Lax342547Proofs.MomentRecovery.rank_add_le _ _).trans
  apply Nat.add_le_add
  · exact (Matrix.rank_mul_le_left _ _).trans_eq (Matrix.rank_transpose _)
  · exact Matrix.rank_mul_le_right _ _

/--
---
conclusion: Lax342547.ResponseMatrices.quotient_projection
---
-/
theorem quotient_projection {B : Type} [Fintype B]
    (S : Submodule Binary (B → Binary)) : by
      classical
      exact ∃ A : Matrix B B Binary, S ≤ LinearMap.ker A.mulVecLin ∧
        (1 - A).rank ≤ Module.finrank Binary S := by
  classical
  obtain ⟨p, hp, hfix, _⟩ := Lax342547Proofs.PrimalRetractions.preserving_retraction S ⊤ (by simp)
  let A := LinearMap.toMatrix' (LinearMap.id - p)
  have he : A.mulVecLin = LinearMap.id - p := LinearMap.toMatrix'.symm_apply_apply _
  refine ⟨A, ?_, ?_⟩
  · intro v hv
    rw [LinearMap.mem_ker, he]
    simp [hfix v hv]
  · have hdiff : 1 - A = LinearMap.toMatrix' p := by
      simp [A, map_sub]
    rw [hdiff, Lax342547.ResponseMatrices.toMatrix_rank]
    apply Submodule.finrank_mono
    rintro _ ⟨v, rfl⟩
    exact hp v

open Lax342547.PairedAnnihilators Lax342547.TableSpaces
open Lax342547.ProjectedPins

/--
---
conclusion: Lax342547.ResponseMatrices.projected_endpoint_response
---
-/
theorem projected_endpoint_response {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H)) (i : Fin 2) (M A C : Matrix B B Binary)
    (hD : D.map (primalProjection i) ≤ LinearMap.ker A.mulVecLin)
    (hE : E.map (primalProjection i) ≤ LinearMap.ker C.mulVecLin) :
    ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = (matrixPair (A.transpose * M * C)).comp (LinearMap.proj i) := by
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
  refine ⟨β, ?_⟩
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
conclusion: Lax342547.ResponseMatrices.projected_paired_response
---
-/
theorem projected_paired_response {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H)) (M A C : Fin 2 → Matrix B B Binary)
    (hD : ∀ i, D.map (primalProjection i) ≤ LinearMap.ker (A i).mulVecLin)
    (hE : ∀ i, E.map (primalProjection i) ≤ LinearMap.ker (C i).mulVecLin) :
    ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = ∑ i, (matrixPair ((A i).transpose * M i * C i)).comp (LinearMap.proj i) := by
  classical
  have he : ∀ i, ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = (matrixPair ((A i).transpose * M i * C i)).comp (LinearMap.proj i) := by
    intro i
    exact Lax342547.ResponseMatrices.projected_endpoint_response D E i (M i) (A i) (C i) (hD i) (hE i)
  choose β hβ using he
  let L : ((Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary) →ₗ[Binary]
      Module.Dual Binary (Fin 2 → Matrix B B Binary) :=
    { toFun := pureResponse D E
      map_add' := Lax342547Proofs.ResponseSolvability.pure_add D E
      map_smul' := Lax342547Proofs.ResponseSolvability.pure_smul D E }
  refine ⟨∑ i, β i, ?_⟩
  change L (∑ i, β i) = _
  rw [map_sum]
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk, hβ]

open Lax342547.TagGeometry Lax342547.ConcreteCut Lax342547.PairedWitnesses Lax342547.CutProfiles
open Lax342547.ExactPins Lax342547.BarredSpaces

/--
---
conclusion: Lax342547.ResponseMatrices.projected_pin_key_dimension
---
-/
theorem projected_pin_key_dimension {k n b degree r K : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (i : Fin 2) (a : Component (Tag k) × Bool) :
    Module.finrank Binary ↥(projected P i a ⊔ individualKeys W i a.1) ≤ K + 14 := by
  classical
  have hp : Module.finrank Binary (projected P i a) ≤ K :=
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans
      (Lax342547.ProjectedPins.projected_rank P i)).trans hK
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
    (Nat.add_le_add hp (Lax342547.BarredSpaces.individual_key_dimension W i a.1))

/--
---
conclusion: Lax342547.ResponseMatrices.actual_pure_projection
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
      ∀ i, (M i - (A i).transpose * M i * C i).rank ≤ 2 * K + 28 ∧
        ((A i).transpose * M i * C i).rank ≤ (M i).rank := by
  classical
  have hAp : ∀ i, ∃ A : Moment k n b degree,
      projected P i (e, true) ⊔ individualKeys W i e ≤ LinearMap.ker A.mulVecLin ∧
      (1 - A).rank ≤ Module.finrank Binary ↥(projected P i (e, true) ⊔ individualKeys W i e) := by
    intro i
    exact Lax342547.ResponseMatrices.quotient_projection _
  have hCp : ∀ i, ∃ C : Moment k n b degree,
      projected P i (e, false) ⊔ individualKeys W i e ≤ LinearMap.ker C.mulVecLin ∧
      (1 - C).rank ≤ Module.finrank Binary ↥(projected P i (e, false) ⊔ individualKeys W i e) := by
    intro i
    exact Lax342547.ResponseMatrices.quotient_projection _
  choose A hA hrA using hAp
  choose C hC hrC using hCp
  have hD : ∀ i, (barred W P U (e, true)).map (primalProjection i) ≤ LinearMap.ker (A i).mulVecLin := by
    intro i
    exact (Lax342547.BarredSpaces.barred_projection W P U (e, true) i).trans (hA i)
  have hE : ∀ i, (barred W P V (e, false)).map (primalProjection i) ≤ LinearMap.ker (C i).mulVecLin := by
    intro i
    exact (Lax342547.BarredSpaces.barred_projection W P V (e, false) i).trans (hC i)
  obtain ⟨β, hβ⟩ := Lax342547.ResponseMatrices.projected_paired_response _ _ M A C hD hE
  refine ⟨A, C, β, hβ, ?_⟩
  intro i
  constructor
  · have ha := (hrA i).trans (Lax342547.ResponseMatrices.projected_pin_key_dimension W P hK i (e, true))
    have hc := (hrC i).trans (Lax342547.ResponseMatrices.projected_pin_key_dimension W P hK i (e, false))
    have hh := (Lax342547.ResponseMatrices.projection_difference_rank (A i) (M i) (C i)).trans (Nat.add_le_add ha hc)
    omega
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/--
---
conclusion: Lax342547.ResponseMatrices.ambient_matrix_representation
---
-/
theorem ambient_matrix_representation {Comp B : Type} [Fintype Comp] [Fintype B]
    (t : (Comp → Matrix B B Binary) →ₗ[Binary] Binary) :
    ∃ M : Comp → Matrix B B Binary, ∀ x, t x = ∑ e, matrixPair (M e) (x e) := by
  classical
  let M : Comp → Matrix B B Binary := fun e a b => t (Pi.single e (Pi.single a (Pi.single b 1)))
  refine ⟨M, ?_⟩
  intro x
  have hx : x = ∑ e, ∑ a, ∑ b, x e a b • Pi.single e (Pi.single a (Pi.single b 1)) := by
    ext e a b
    simp [Pi.single_apply, Finset.sum_apply, ite_apply]
  have he := congrArg t hx
  simp only [map_sum, map_smul, smul_eq_mul] at he
  rw [he]
  simp [M, matrixPair, matrixEntry, mul_comm]

/--
---
conclusion: Lax342547.ResponseMatrices.matrix_representation
---
-/
theorem matrix_representation {Comp B : Type} [Fintype Comp] [Fintype B]
    (X : Submodule Binary (Comp → Matrix B B Binary)) (t : X →ₗ[Binary] Binary) :
    ∃ M : Comp → Matrix B B Binary, ∀ x : X, t x = ∑ e, matrixPair (M e) (x.val e) := by
  obtain ⟨t', ht⟩ := t.exists_extend
  obtain ⟨M, hM⟩ := Lax342547.ResponseMatrices.ambient_matrix_representation t'
  refine ⟨M, ?_⟩
  intro x
  have he := DFunLike.congr_fun ht x
  change t' x.val = t x at he
  rw [← he, hM]

/--
---
conclusion: Lax342547.ResponseMatrices.comp_left_rank
---
-/
theorem comp_left_rank {A V X : Type} [AddCommGroup A] [Module Binary A]
    [AddCommGroup V] [Module Binary V] [AddCommGroup X] [Module Binary X]
    [FiniteDimensional Binary X] (f : A →ₗ[Binary] X) (g : V →ₗ[Binary] A) :
    Module.finrank Binary (LinearMap.range (f.comp g)) ≤ Module.finrank Binary (LinearMap.range f) := by
  apply Submodule.finrank_mono
  rintro _ ⟨v, rfl⟩
  exact ⟨g v, rfl⟩

/--
---
conclusion: Lax342547.ResponseMatrices.comp_right_rank
---
-/
theorem comp_right_rank {A V X : Type} [AddCommGroup A] [Module Binary A]
    [AddCommGroup V] [Module Binary V] [AddCommGroup X] [Module Binary X]
    [FiniteDimensional Binary A] (f : A →ₗ[Binary] X) (g : V →ₗ[Binary] A) :
    Module.finrank Binary (LinearMap.range (f.comp g)) ≤ Module.finrank Binary (LinearMap.range g) := by
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

open Lax342547.DerivativeResponses Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.NominalPrimal Lax342547.TensorAnnihilators

/--
---
conclusion: Lax342547.ResponseMatrices.restriction_rank
---
-/
theorem restriction_rank {B H : Type} [Fintype B] [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (i : Fin 2) :
    Module.finrank Binary (LinearMap.range (restriction D S δ i)) ≤
      Module.finrank Binary (LinearMap.range δ) := by
  change Module.finrank Binary (LinearMap.range
    ((perpendicular S).subtype.comp (δ.comp (D.mkQ.comp (primalEmbedding i))))) ≤ _
  exact (Lax342547.ResponseMatrices.comp_right_rank _ _).trans (Lax342547.ResponseMatrices.comp_left_rank _ _)

/--
---
conclusion: Lax342547.ResponseMatrices.baseline_coordinate_rank
---
-/
theorem baseline_coordinate_rank {Comp B H : Type} [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2) (R : ℕ)
    (hplus : Module.finrank Binary (LinearMap.range ((F.forward e).compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R)
    (hminus : Module.finrank Binary (LinearMap.range ((F.reverse e).flip.compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R) :
    ∀ i, Module.finrank Binary (LinearMap.range (fullPlus F e i z)) ≤ R ∧
      Module.finrank Binary (LinearMap.range (fullMinus F e i z)) ≤ R := by
  classical
  intro i
  let j : (B → Binary) →ₗ[Binary] primal (B := B) (H := H) :=
    (primalEmbedding i).codRestrict primal (by intro v a h; simp [primalEmbedding])
  let Cplus := (F.forward e).compl₁₂ (primal (B := B) (H := H)).subtype (channelEmbedding z)
  let Cminus := (F.reverse e).flip.compl₁₂ (primal (B := B) (H := H)).subtype (channelEmbedding z)
  have heplus : fullPlus F e i z = dualCoordinates.comp (Cplus.comp j) := by
    apply LinearMap.ext
    intro v
    funext h
    rfl
  have heminus : fullMinus F e i z = dualCoordinates.comp (Cminus.comp j) := by
    apply LinearMap.ext
    intro v
    funext h
    rfl
  constructor
  · rw [heplus]
    exact ((Lax342547.ResponseMatrices.comp_right_rank _ _).trans (Lax342547.ResponseMatrices.comp_left_rank _ _)).trans hplus
  · rw [heminus]
    exact ((Lax342547.ResponseMatrices.comp_right_rank _ _).trans (Lax342547.ResponseMatrices.comp_left_rank _ _)).trans hminus

/--
---
conclusion: Lax342547.ResponseMatrices.extra_product_response
---
-/
theorem extra_product_response {B H : Type} [Fintype B] [Fintype H]
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T) :
    pureResponse D E (extraProduct D E S T δ ε) =
      ∑ i, (matrixPair (coefficients (restriction D S δ i) (restriction E T ε i))).comp (LinearMap.proj i) := by
  rfl

/--
---
conclusion: Lax342547.ResponseMatrices.rank_sub_le
---
-/
theorem rank_sub_le {B : Type} [Fintype B] (M C : Matrix B B Binary) :
    (M - C).rank ≤ M.rank + C.rank := by
  have hneg : -C = C := neg_eq_iff_add_eq_zero.mpr (ZModModule.add_self C)
  rw [sub_eq_add_neg, hneg]
  exact Lax342547Proofs.MomentRecovery.rank_add_le _ _

/--
---
conclusion: Lax342547.ResponseMatrices.bounded_residual_rank
---
-/
theorem bounded_residual_rank {B H : Type} [Fintype B] [Fintype H] (K : ℕ)
    (M Q : Matrix B B Binary) (hM : (M - Q).rank ≤ 2 * K + 28)
    (f g df dg : (B → Binary) →ₗ[Binary] (H → Binary))
    (hf : Module.finrank Binary (LinearMap.range f) ≤ 3 * K + 28)
    (hdf : Module.finrank Binary (LinearMap.range df) ≤ 3 * K + 28) :
    (residualCoefficients M Q f g df dg).rank ≤ 14 * K + 140 := by
  have hb := ((Lax342547.ResponseMatrices.coefficients_rank f g).trans (min_le_left _ _)).trans hf
  have hδf := ((Lax342547.ResponseMatrices.coefficients_rank df g).trans (min_le_left _ _)).trans hdf
  have hδg := ((Lax342547.ResponseMatrices.coefficients_rank f dg).trans (min_le_left _ _)).trans hf
  have hprod := ((Lax342547.ResponseMatrices.coefficients_rank df dg).trans (min_le_left _ _)).trans hdf
  have h1 := Lax342547.ResponseMatrices.rank_sub_le (M - Q) (coefficients f g)
  have h2 := Lax342547.ResponseMatrices.rank_sub_le (M - Q - coefficients f g) (coefficients df g)
  have h3 := Lax342547.ResponseMatrices.rank_sub_le (M - Q - coefficients f g - coefficients df g) (coefficients f dg)
  have h4 := Lax342547.ResponseMatrices.rank_sub_le (M - Q - coefficients f g - coefficients df g - coefficients f dg) (coefficients df dg)
  unfold residualCoefficients
  omega

end Lax342547Proofs.ResponseMatrices
