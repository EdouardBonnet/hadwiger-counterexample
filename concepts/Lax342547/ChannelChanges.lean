import Lax342547.PrimalContractions
import Lax342547.TableContractions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
---
title: Allowed channel changes and the actual table injection tests
type: lemma
---
Channel changes factor through a frozen nominal quotient and take values
orthogonal to the opposite protected channel. They preserve the frozen
entries and vanish on opposite primal inputs. Orthogonal channel tests
and the actual table injection flags force a pinned primal vector to zero.
`DerivativeResponses` derives these tests from the full derivative response.
-/

namespace Lax342547.ChannelChanges

open Lax342547.MomentSpace Lax342547.TableSpaces Lax342547.PairedAnnihilators
open Lax342547.PrimalContractions Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.SmallTables Lax342547.TableContractions
open Lax342547.TensorAnnihilators

def perpendicular {H : Type} [Fintype H] (S : Submodule Binary (H → Binary)) :
    Submodule Binary (H → Binary) :=
  LinearMap.BilinForm.orthogonal (dotProductBilin Binary Binary) S

def channelChange {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z : Fin 2) :
    LinearMap.BilinForm Binary (Nominal B H) :=
  (dotProductBilin Binary Binary).compl₁₂
    (((perpendicular S).subtype.comp δ).comp D.mkQ) (channelProjection z)

axiom frozen {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z : Fin 2)
    (v w : Nominal B H) (h : v ∈ D ∨ channelProjection z w ∈ S) :
    channelChange D S δ z v w = 0

axiom opposite_primal {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z j : Fin 2)
    (v : Nominal B H) (w : B → Binary) :
    channelChange D S δ z v (primalEmbedding j w) = 0

axiom pin_frozen {Comp B H N : Type} [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (D : Submodule Binary (Nominal B H)) (a : Comp × Bool) (z : Fin 2)
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular (protectedChannel P z a))
    (v w : Nominal B H) (hw : w ∈ P.space a) :
    channelChange D (protectedChannel P z a) δ z v w = 0

axiom perpendicular_detects {H : Type} [Fintype H]
    (S : Submodule Binary (H → Binary)) (v : H → Binary)
    (h : ∀ c ∈ perpendicular S, dotProduct v c = 0) : v ∈ S

axiom row_injection_zero {Comp B H N : Type} [Fintype H]
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (hT : Injecting T) (F : CrossForms Comp B H) (hF : Extends F T)
    (e : Comp) (i z : Fin 2) (d : pinnedPrimal P i (e, true))
    (h : ∀ c ∈ perpendicular (protectedChannel Q z (e, true)),
      dotProduct (fullPlus F e i z d.val) c = 0) : d.val = 0

axiom column_injection_zero {Comp B H N : Type} [Fintype H]
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (hT : Injecting T) (F : CrossForms Comp B H) (hF : Extends F T)
    (e : Comp) (i z : Fin 2) (d : pinnedPrimal P i (e, false))
    (h : ∀ c ∈ perpendicular (protectedChannel Q z (e, false)),
      dotProduct (fullMinus F e i z d.val) c = 0) : d.val = 0

axiom channel_entry {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z : Fin 2)
    (v : Nominal B H) (h : H) : by
      classical
      exact channelChange D S δ z v (channelEmbedding z (Pi.single h 1)) =
        (δ (D.mkQ v)).val h

end Lax342547.ChannelChanges
