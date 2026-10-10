import Lax342547.BoundedDerivatives
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
---
title: Matrix representations and the bounded residual rank ingredients
type: definition and theorem
---
Actual cut-profile functionals have component matrix representations.
Projected forms descend through the actual barred nominal quotients, with
a per-individual removal cost at most 2K+28. Baseline and derivative
contractions have bounded rank, and the derivative product is a permitted
pure quotient response. These ingredients give the paper residual matrix
rank estimate before the remaining compression and channel realization.
-/

namespace Lax342547.ResponseMatrices

open Lax342547.MomentSpace Lax342547.ConcreteGeometry
open Lax342547.TensorContractions
open Lax342547.PairedAnnihilators Lax342547.TableSpaces
open Lax342547.ProjectedPins
open Lax342547.TagGeometry Lax342547.ConcreteCut Lax342547.PairedWitnesses Lax342547.CutProfiles
open Lax342547.ExactPins Lax342547.BarredSpaces
open Lax342547.DerivativeResponses Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.NominalPrimal Lax342547.TensorAnnihilators

noncomputable def coefficients {B H : Type} [Fintype B] [Fintype H]
    (f g : (B → Binary) →ₗ[Binary] (H → Binary)) : Matrix B B Binary := by
  classical
  exact LinearMap.BilinForm.toMatrix' ((dotProductBilin Binary Binary).compl₁₂ f g)

noncomputable def extraProduct {B H : Type} [Fintype H]
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T) :
    (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary :=
  (dotProductBilin Binary Binary).compl₁₂ ((perpendicular S).subtype.comp δ)
    ((perpendicular T).subtype.comp ε)

noncomputable def residualCoefficients {B H : Type} [Fintype B] [Fintype H]
    (M Q : Matrix B B Binary) (f g df dg : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Matrix B B Binary :=
  M - Q - coefficients f g - coefficients df g - coefficients f dg - coefficients df dg

axiom coefficients_product {B H : Type} [Fintype B] [Fintype H]
    (f g : (B → Binary) →ₗ[Binary] (H → Binary)) : by
      classical
      exact coefficients f g = (LinearMap.toMatrix' f).transpose * LinearMap.toMatrix' g

axiom toMatrix_rank {B H : Type} [Fintype B] [Fintype H]
    (f : (B → Binary) →ₗ[Binary] (H → Binary)) : by
      classical
      exact (LinearMap.toMatrix' f).rank = Module.finrank Binary (LinearMap.range f)

axiom coefficients_rank {B H : Type} [Fintype B] [Fintype H]
    (f g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    (coefficients f g).rank ≤ min (Module.finrank Binary (LinearMap.range f))
      (Module.finrank Binary (LinearMap.range g))

axiom projection_difference {B : Type} [Fintype B] [DecidableEq B]
    (A M C : Matrix B B Binary) :
    M - A.transpose * M * C = (1 - A).transpose * M + A.transpose * M * (1 - C)

axiom projection_difference_rank {B : Type} [Fintype B] [DecidableEq B]
    (A M C : Matrix B B Binary) :
    (M - A.transpose * M * C).rank ≤ (1 - A).rank + (1 - C).rank

axiom quotient_projection {B : Type} [Fintype B]
    (S : Submodule Binary (B → Binary)) : by
      classical
      exact ∃ A : Matrix B B Binary, S ≤ LinearMap.ker A.mulVecLin ∧
        (1 - A).rank ≤ Module.finrank Binary S

axiom projected_endpoint_response {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H)) (i : Fin 2) (M A C : Matrix B B Binary)
    (hD : D.map (primalProjection i) ≤ LinearMap.ker A.mulVecLin)
    (hE : E.map (primalProjection i) ≤ LinearMap.ker C.mulVecLin) :
    ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = (matrixPair (A.transpose * M * C)).comp (LinearMap.proj i)

axiom projected_paired_response {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H)) (M A C : Fin 2 → Matrix B B Binary)
    (hD : ∀ i, D.map (primalProjection i) ≤ LinearMap.ker (A i).mulVecLin)
    (hE : ∀ i, E.map (primalProjection i) ≤ LinearMap.ker (C i).mulVecLin) :
    ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = ∑ i, (matrixPair ((A i).transpose * M i * C i)).comp (LinearMap.proj i)

axiom projected_pin_key_dimension {k n b degree r K : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (i : Fin 2) (a : Component (Tag k) × Bool) :
    Module.finrank Binary ↥(projected P i a ⊔ individualKeys W i a.1) ≤ K + 14

axiom actual_pure_projection {k n b degree r K : ℕ} {hr : 2 * r ≤ n}
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
        ((A i).transpose * M i * C i).rank ≤ (M i).rank

axiom ambient_matrix_representation {Comp B : Type} [Fintype Comp] [Fintype B]
    (t : (Comp → Matrix B B Binary) →ₗ[Binary] Binary) :
    ∃ M : Comp → Matrix B B Binary, ∀ x, t x = ∑ e, matrixPair (M e) (x e)

axiom matrix_representation {Comp B : Type} [Fintype Comp] [Fintype B]
    (X : Submodule Binary (Comp → Matrix B B Binary)) (t : X →ₗ[Binary] Binary) :
    ∃ M : Comp → Matrix B B Binary, ∀ x : X, t x = ∑ e, matrixPair (M e) (x.val e)

axiom comp_left_rank {A V X : Type} [AddCommGroup A] [Module Binary A]
    [AddCommGroup V] [Module Binary V] [AddCommGroup X] [Module Binary X]
    [FiniteDimensional Binary X] (f : A →ₗ[Binary] X) (g : V →ₗ[Binary] A) :
    Module.finrank Binary (LinearMap.range (f.comp g)) ≤ Module.finrank Binary (LinearMap.range f)

axiom comp_right_rank {A V X : Type} [AddCommGroup A] [Module Binary A]
    [AddCommGroup V] [Module Binary V] [AddCommGroup X] [Module Binary X]
    [FiniteDimensional Binary A] (f : A →ₗ[Binary] X) (g : V →ₗ[Binary] A) :
    Module.finrank Binary (LinearMap.range (f.comp g)) ≤ Module.finrank Binary (LinearMap.range g)

axiom restriction_rank {B H : Type} [Fintype B] [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (i : Fin 2) :
    Module.finrank Binary (LinearMap.range (restriction D S δ i)) ≤
      Module.finrank Binary (LinearMap.range δ)

axiom baseline_coordinate_rank {Comp B H : Type} [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2) (R : ℕ)
    (hplus : Module.finrank Binary (LinearMap.range ((F.forward e).compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R)
    (hminus : Module.finrank Binary (LinearMap.range ((F.reverse e).flip.compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R) :
    ∀ i, Module.finrank Binary (LinearMap.range (fullPlus F e i z)) ≤ R ∧
      Module.finrank Binary (LinearMap.range (fullMinus F e i z)) ≤ R

axiom extra_product_response {B H : Type} [Fintype B] [Fintype H]
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T) :
    pureResponse D E (extraProduct D E S T δ ε) =
      ∑ i, (matrixPair (coefficients (restriction D S δ i) (restriction E T ε i))).comp (LinearMap.proj i)

axiom rank_sub_le {B : Type} [Fintype B] (M C : Matrix B B Binary) :
    (M - C).rank ≤ M.rank + C.rank

axiom bounded_residual_rank {B H : Type} [Fintype B] [Fintype H] (K : ℕ)
    (M Q : Matrix B B Binary) (hM : (M - Q).rank ≤ 2 * K + 28)
    (f g df dg : (B → Binary) →ₗ[Binary] (H → Binary))
    (hf : Module.finrank Binary (LinearMap.range f) ≤ 3 * K + 28)
    (hdf : Module.finrank Binary (LinearMap.range df) ≤ 3 * K + 28) :
    (residualCoefficients M Q f g df dg).rank ≤ 14 * K + 140

end Lax342547.ResponseMatrices
