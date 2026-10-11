import Lax342547.BaseCompression
import Lax342547.ResidualRealization

/-!
---
title: Compression on the actual barred nominal quotients
type: lemma
---
Base compression fixes frozen pins, selected keys, and private channels. It descends through the actual barred spaces with the paper quotient-rank bound, and precomposition bounds a pure bilinear form while retaining its response on compressed component matrices.
-/

namespace Lax342547.QuotientCompression

open Lax342547.MomentSpace Lax342547.PairedAnnihilators
open Lax342547.TableSpaces Lax342547.ProjectedPins Lax342547.BaseCompression
open Lax342547.TagGeometry Lax342547.ConcreteGeometry Lax342547.ConcreteCut
open Lax342547.PairedWitnesses Lax342547.ExactPins Lax342547.BarredSpaces
open Lax342547.CutProfiles

def nominalLift {B H : Type} (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary)) :
    Nominal B H →ₗ[Binary] Nominal B H where
  toFun v q := match q.2 with
    | Sum.inl b => f q.1 (primalProjection q.1 v) b
    | Sum.inr h => v (q.1, Sum.inr h)
  map_add' v w := by
    ext ⟨i, b | h⟩
    · exact congrFun ((f i).map_add _ _) b
    · rfl
  map_smul' c v := by
    ext ⟨i, b | h⟩
    · exact congrFun ((f i).map_smul c _) b
    · rfl

axiom nominalLift_primal {B H : Type}
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary)) (i : Fin 2) (v : B → Binary) :
    nominalLift (H := H) f (primalEmbedding i v) = primalEmbedding i (f i v)

axiom nominalLift_fix {B H : Type}
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary)) (v : Nominal B H)
    (h : ∀ i, f i (primalProjection i v) = primalProjection i v) : nominalLift f v = v

axiom nominalLift_sum {B H : Type}
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary)) (v : Nominal B H) :
    nominalLift f v = ∑ i, (primalEmbedding i (f i (primalProjection i v)) +
      channelEmbedding i (channelProjection i v))

axiom barred_fixed {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}
    (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (a : Component (Tag k) × Bool)
    (f : Fin 2 → Vector k n b degree →ₗ[Binary] Vector k n b degree)
    (hfix : ∀ i v, v ∈ projected P i a ⊔ individualKeys W i a.1 → f i v = v) :
    ∀ v ∈ barred W P U a, nominalLift f v = v

axiom quotient_lift_rank {B H : Type} [Fintype B] [Fintype H]
    (D : Submodule Binary (Nominal B H))
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary))
    (hD : D ≤ D.comap (nominalLift f))
    (S U : Fin 2 → Submodule Binary (H → Binary))
    (hcompl : ∀ i, IsCompl (S i) (U i))
    (hprivate : ∀ i, (U i).map (channelEmbedding (B := B) i) ≤ D) :
    Module.finrank Binary (LinearMap.range (D.mapQ D (nominalLift f) hD)) ≤
      ∑ i, (Module.finrank Binary (LinearMap.range (f i)) + Module.finrank Binary (S i))

axiom barred_compression {k n b degree r K Dblk : ℕ} {hr : 2 * r ≤ n}
    {H N : Type} [Fintype H] (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (a : Component (Tag k) × Bool)
    (U : Fin 2 → Submodule Binary (H → Binary))
    (hcompl : ∀ i, IsCompl (protectedChannel P i a) (U i))
    (A : Fin 2 → Block k → (Fin n → Binary) →ₗ[Binary] (Fin n → Binary))
    (hA : ∀ i q, Module.finrank Binary (LinearMap.range (A i q)) ≤ Dblk)
    (hfix : ∀ i v, v ∈ projected P i a ⊔ individualKeys W i a.1 →
      liftBase (blockMap (A i)) v = v) :
    ∃ q : (Nominal (Coordinate k n b degree) H ⧸ barred W P U a) →ₗ[Binary]
        (Nominal (Coordinate k n b degree) H ⧸ barred W P U a),
      (∀ v, q ((barred W P U a).mkQ v) = (barred W P U a).mkQ
        (nominalLift (fun i => liftBase (blockMap (A i))) v)) ∧
      Module.finrank Binary (LinearMap.range q) ≤
        2 * Fintype.card (SelectorCoordinates b degree) *
          (1 + ((2 * k + 1)^2 + 3) * Dblk) + 2 * K

axiom compressed_bilinear_rank {A B : Type} [AddCommGroup A] [Module Binary A]
    [AddCommGroup B] [Module Binary B] [FiniteDimensional Binary A]
    (β : A →ₗ[Binary] B →ₗ[Binary] Binary) (q : A →ₗ[Binary] A) (p : B →ₗ[Binary] B) :
    Module.finrank Binary (LinearMap.range (β.compl₁₂ q p)) ≤
      Module.finrank Binary (LinearMap.range q)

axiom pure_compressed {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H))
    (β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary)
    (f : Fin 2 → (B → Binary) →ₗ[Binary] (B → Binary))
    (qD : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ D))
    (qE : (Nominal B H ⧸ E) →ₗ[Binary] (Nominal B H ⧸ E))
    (hD : ∀ v, qD (D.mkQ v) = D.mkQ (nominalLift f v))
    (hE : ∀ v, qE (E.mkQ v) = E.mkQ (nominalLift f v))
    (x : Fin 2 → Matrix B B Binary) :
    pureResponse D E (β.compl₁₂ qD qE) x =
      pureResponse D E β (fun i => tensorMap (f i) (x i))

end Lax342547.QuotientCompression
