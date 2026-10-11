import Lax342547.CompressedResidual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Projective

/-!
---
title: Rank-controlled factorization through allowed orthogonal channels
type: lemma
---
A pure quotient form factors through the actual dot pairing whenever its rank fits. Orthogonality to protected channels, baseline values and bounded derivative values costs at most K+2R on each side. The resulting allowed maps realize the pure form exactly and have all required vanishing cross pairings; simultaneous gradient assembly and target routing remain separate.
-/

namespace Lax342547.ChannelFactorization

open Lax342547.MomentSpace Lax342547.ChannelChanges
open Lax342547.PairedAnnihilators Lax342547.ResponseMatrices

axiom factor_through_pairing {X Y U V : Type}
    [AddCommGroup X] [Module Binary X] [AddCommGroup Y] [Module Binary Y]
    [AddCommGroup U] [Module Binary U] [AddCommGroup V] [Module Binary V]
    [FiniteDimensional Binary Y] [FiniteDimensional Binary V]
    (β : X →ₗ[Binary] Y →ₗ[Binary] Binary) (π : U →ₗ[Binary] V →ₗ[Binary] Binary)
    (hr : Module.finrank Binary (LinearMap.range β) ≤ Module.finrank Binary (LinearMap.range π)) :
    ∃ f : X →ₗ[Binary] U, ∃ g : Y →ₗ[Binary] V, π.compl₁₂ f g = β

axiom factor_in_channel_spaces {X Y H : Type} [Fintype H]
    [AddCommGroup X] [Module Binary X] [AddCommGroup Y] [Module Binary Y]
    [FiniteDimensional Binary Y]
    (S T : Submodule Binary (H → Binary)) (β : X →ₗ[Binary] Y →ₗ[Binary] Binary)
    (hr : Module.finrank Binary (LinearMap.range β) ≤ Module.finrank Binary
      (LinearMap.range ((dotProductBilin Binary Binary).compl₁₂ S.subtype T.subtype))) :
    ∃ f : X →ₗ[Binary] S, ∃ g : Y →ₗ[Binary] T,
      (dotProductBilin Binary Binary).compl₁₂ (S.subtype.comp f) (T.subtype.comp g) = β

axiom perpendicular_dimension {H : Type} [Fintype H] (S : Submodule Binary (H → Binary)) :
    Module.finrank Binary S + Module.finrank Binary (perpendicular S) = Fintype.card H

axiom channel_pairing_rank {H : Type} [Fintype H]
    (S T : Submodule Binary (H → Binary)) {cS cT : ℕ}
    (hS : Fintype.card H ≤ Module.finrank Binary S + cS)
    (hT : Fintype.card H ≤ Module.finrank Binary T + cT) :
    Fintype.card H ≤ Module.finrank Binary
      (LinearMap.range ((dotProductBilin Binary Binary).compl₁₂ S.subtype T.subtype)) + cS + cT

noncomputable def remainingValues {A B H : Type} [Fintype H]
    [AddCommGroup A] [Module Binary A] [AddCommGroup B] [Module Binary B]
    (S : Submodule Binary (H → Binary)) (G : A →ₗ[Binary] (H → Binary))
    (D : B →ₗ[Binary] (H → Binary)) : Submodule Binary (H → Binary) :=
  perpendicular (S ⊔ LinearMap.range G ⊔ LinearMap.range D)

axiom remaining_values_dimension {A B H : Type} [Fintype H]
    [AddCommGroup A] [Module Binary A] [AddCommGroup B] [Module Binary B]
    (S : Submodule Binary (H → Binary)) (G : A →ₗ[Binary] (H → Binary))
    (D : B →ₗ[Binary] (H → Binary)) {K R : ℕ}
    (hS : Module.finrank Binary S ≤ K)
    (hG : Module.finrank Binary (LinearMap.range G) ≤ R)
    (hD : Module.finrank Binary (LinearMap.range D) ≤ R) :
    Fintype.card H ≤ Module.finrank Binary (remainingValues S G D) + (K + 2 * R)

axiom remaining_values_allowed {A B H : Type} [Fintype H]
    [AddCommGroup A] [Module Binary A] [AddCommGroup B] [Module Binary B]
    (S : Submodule Binary (H → Binary)) (G : A →ₗ[Binary] (H → Binary))
    (D : B →ₗ[Binary] (H → Binary)) : remainingValues S G D ≤ perpendicular S

axiom remaining_values_orthogonal {A B H : Type} [Fintype H]
    [AddCommGroup A] [Module Binary A] [AddCommGroup B] [Module Binary B]
    (S : Submodule Binary (H → Binary)) (G : A →ₗ[Binary] (H → Binary))
    (D : B →ₗ[Binary] (H → Binary)) (v : remainingValues S G D) :
    (∀ a, dotProduct v.val (G a) = 0) ∧ (∀ b, dotProduct v.val (D b) = 0)

axiom remaining_values_factor {X Y A B C D H : Type} [Fintype H]
    [AddCommGroup X] [Module Binary X] [AddCommGroup Y] [Module Binary Y]
    [AddCommGroup A] [Module Binary A] [AddCommGroup B] [Module Binary B]
    [AddCommGroup C] [Module Binary C] [AddCommGroup D] [Module Binary D]
    [FiniteDimensional Binary Y]
    (S T : Submodule Binary (H → Binary))
    (G : A →ₗ[Binary] (H → Binary)) (dG : B →ₗ[Binary] (H → Binary))
    (F : C →ₗ[Binary] (H → Binary)) (dF : D →ₗ[Binary] (H → Binary))
    (β : X →ₗ[Binary] Y →ₗ[Binary] Binary) {K R : ℕ}
    (hS : Module.finrank Binary S ≤ K) (hT : Module.finrank Binary T ≤ K)
    (hG : Module.finrank Binary (LinearMap.range G) ≤ R)
    (hdG : Module.finrank Binary (LinearMap.range dG) ≤ R)
    (hF : Module.finrank Binary (LinearMap.range F) ≤ R)
    (hdF : Module.finrank Binary (LinearMap.range dF) ≤ R)
    (hcapacity : Module.finrank Binary (LinearMap.range β) + 2 * K + 4 * R ≤ Fintype.card H) :
    ∃ f : X →ₗ[Binary] remainingValues S G dG,
    ∃ g : Y →ₗ[Binary] remainingValues T F dF,
      (dotProductBilin Binary Binary).compl₁₂
        ((remainingValues S G dG).subtype.comp f) ((remainingValues T F dF).subtype.comp g) = β

axiom allowed_pure_factor {B H A C E F : Type} [Fintype B] [Fintype H]
    [AddCommGroup A] [Module Binary A] [AddCommGroup C] [Module Binary C]
    [AddCommGroup E] [Module Binary E] [AddCommGroup F] [Module Binary F]
    (D Q : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (G : A →ₗ[Binary] (H → Binary)) (dG : C →ₗ[Binary] (H → Binary))
    (G' : E →ₗ[Binary] (H → Binary)) (dG' : F →ₗ[Binary] (H → Binary))
    (β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ Q) →ₗ[Binary] Binary) {K R : ℕ}
    (hS : Module.finrank Binary S ≤ K) (hT : Module.finrank Binary T ≤ K)
    (hG : Module.finrank Binary (LinearMap.range G) ≤ R)
    (hdG : Module.finrank Binary (LinearMap.range dG) ≤ R)
    (hG' : Module.finrank Binary (LinearMap.range G') ≤ R)
    (hdG' : Module.finrank Binary (LinearMap.range dG') ≤ R)
    (hcapacity : Module.finrank Binary (LinearMap.range β) + 2 * K + 4 * R ≤ Fintype.card H) :
    ∃ δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S,
    ∃ ε : (Nominal B H ⧸ Q) →ₗ[Binary] perpendicular T,
      extraProduct D Q S T δ ε = β ∧
      (∀ x a, dotProduct (δ x).val (G a) = 0) ∧
      (∀ x c, dotProduct (δ x).val (dG c) = 0) ∧
      (∀ y e, dotProduct (ε y).val (G' e) = 0) ∧
      (∀ y f, dotProduct (ε y).val (dG' f) = 0)

end Lax342547.ChannelFactorization
