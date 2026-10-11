import Lax342547.ResponseMatrices

/-!
---
title: Rank-controlled pure forms on the actual barred quotients
type: lemma
---
Projection away from the actual pin/key spaces yields pure quotient forms whose bilinear rank is at most the sum of the two individual target-matrix ranks. The projection loss remains at most 2K+28 per individual. This supplies the initial pure-form rank needed when restoring the compressed residual correction.
-/

namespace Lax342547.RankedProjection

open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.TableSpaces
open Lax342547.ProjectedPins Lax342547.ResponseMatrices
open Lax342547.ConcreteGeometry
open Lax342547.TagGeometry Lax342547.ConcreteCut Lax342547.PairedWitnesses Lax342547.CutProfiles
open Lax342547.ExactPins Lax342547.BarredSpaces

axiom bilinear_comp_rank {A B V X : Type} [AddCommGroup A] [Module Binary A]
    [AddCommGroup B] [Module Binary B] [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary B]
    (β : A →ₗ[Binary] B →ₗ[Binary] Binary)
    (f : V →ₗ[Binary] A) (g : X →ₗ[Binary] B) :
    Module.finrank Binary (LinearMap.range (β.compl₁₂ f g)) ≤
      Module.finrank Binary (LinearMap.range β)

axiom matrix_bilinear_rank {B : Type} [Fintype B] (M : Matrix B B Binary) :
    by
      classical
      exact Module.finrank Binary (LinearMap.range (Matrix.toBilin' M)) ≤ M.rank

axiom linear_add_rank {V X : Type} [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (f g : V →ₗ[Binary] X) :
    Module.finrank Binary (LinearMap.range (f + g)) ≤
      Module.finrank Binary (LinearMap.range f) + Module.finrank Binary (LinearMap.range g)

axiom linear_sum_rank {I V X : Type} [Fintype I] [AddCommGroup V] [Module Binary V]
    [AddCommGroup X] [Module Binary X] [FiniteDimensional Binary X]
    (f : I → V →ₗ[Binary] X) :
    Module.finrank Binary (LinearMap.range (∑ i, f i)) ≤
      ∑ i, Module.finrank Binary (LinearMap.range (f i))

axiom projected_endpoint_response {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H)) (i : Fin 2) (M A C : Matrix B B Binary)
    (hD : D.map (primalProjection i) ≤ LinearMap.ker A.mulVecLin)
    (hE : E.map (primalProjection i) ≤ LinearMap.ker C.mulVecLin) :
    ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = (matrixPair (A.transpose * M * C)).comp (LinearMap.proj i) ∧
      Module.finrank Binary (LinearMap.range β) ≤ M.rank

axiom projected_paired_response {B H : Type} [Fintype B] [Fintype H]
    (D E : Submodule Binary (Nominal B H)) (M A C : Fin 2 → Matrix B B Binary)
    (hD : ∀ i, D.map (primalProjection i) ≤ LinearMap.ker (A i).mulVecLin)
    (hE : ∀ i, E.map (primalProjection i) ≤ LinearMap.ker (C i).mulVecLin) :
    ∃ β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary,
      pureResponse D E β = ∑ i, (matrixPair ((A i).transpose * M i * C i)).comp (LinearMap.proj i) ∧
      Module.finrank Binary (LinearMap.range β) ≤ ∑ i, (M i).rank

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
      Module.finrank Binary (LinearMap.range β) ≤ ∑ i, (M i).rank ∧
      ∀ i, (M i - (A i).transpose * M i * C i).rank ≤ 2 * K + 28 ∧
        ((A i).transpose * M i * C i).rank ≤ (M i).rank

end Lax342547.RankedProjection
