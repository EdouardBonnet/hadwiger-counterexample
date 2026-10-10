import Lax342547.TargetMatrices

/-!
---
title: Pure corrections realized by actual nonlinear channel products
type: definition and theorem
---
Low-rank baseline values use the combined primal space. Orthogonal private factors add the desired pure form to the channel product while retaining the entire derivative response. The paper margin provides sufficient channel capacity. These changes retain their barred domains and permitted perpendicular outputs.
-/

namespace Lax342547.NonlinearChannels

open Lax342547.ConcreteCut
open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges
open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.NominalPrimal Lax342547.TensorAnnihilators

noncomputable def primalValues {B H : Type} [Fintype H]
    (F : LinearMap.BilinForm Binary (Nominal B H)) (z : Fin 2) :
    primal (B := B) (H := H) →ₗ[Binary] (H → Binary) := by
  classical
  exact dualCoordinates.comp (F.compl₁₂ primal.subtype (channelEmbedding z))

axiom primal_values_rank {B H : Type} [Fintype B] [Fintype H]
    (F : LinearMap.BilinForm Binary (Nominal B H)) (z : Fin 2) :
    Module.finrank Binary (LinearMap.range (primalValues F z)) ≤
      Module.finrank Binary (LinearMap.range (F.compl₁₂ primal.subtype (channelEmbedding z)))

def liftPrimal {B H : Type} (i : Fin 2) : (B → Binary) →ₗ[Binary] primal (B := B) (H := H) :=
  (primalEmbedding i).codRestrict primal (by intro v a h; simp [primalEmbedding])

axiom primal_plus_values {Comp B H : Type} [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (i z : Fin 2) (v : B → Binary) :
    primalValues (F.forward e) z (liftPrimal i v) = fullPlus F e i z v

axiom primal_minus_values {Comp B H : Type} [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (i z : Fin 2) (v : B → Binary) :
    primalValues (F.reverse e).flip z (liftPrimal i v) = fullMinus F e i z v

axiom extra_product_add {B H : Type} [Fintype H]
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δ f : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε g : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T)
    (hfg : ∀ x y, dotProduct (f x).val (ε y).val = 0)
    (hgf : ∀ x y, dotProduct (g y).val (δ x).val = 0) :
    extraProduct D E S T (δ + f) (ε + g) =
      extraProduct D E S T δ ε + extraProduct D E S T f g

axiom ambient_add_left {B H : Type} [Fintype B] [Fintype H]
    (f df g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient (f + df) g =
      Lax342547.TensorContractions.ambient f g + Lax342547.TensorContractions.ambient df g

axiom ambient_add_right {B H : Type} [Fintype B] [Fintype H]
    (f g dg : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient f (g + dg) =
      Lax342547.TensorContractions.ambient f g + Lax342547.TensorContractions.ambient f dg

axiom ambient_orthogonal_zero {B H : Type} [Fintype B] [Fintype H]
    (f g : (B → Binary) →ₗ[Binary] (H → Binary))
    (h : ∀ v w, dotProduct (f v) (g w) = 0) :
    Lax342547.TensorContractions.ambient f g = 0

axiom restriction_add {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ f : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (i : Fin 2) :
    restriction D S (δ + f) i = restriction D S δ i + restriction D S f i

axiom component_response_unchanged {Comp B H : Type} [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δ f : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε g : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T)
    (hf : ∀ x (v : primal (B := B) (H := H)),
      dotProduct (f x).val (primalValues (F.reverse e).flip z v) = 0)
    (hg : ∀ y (v : primal (B := B) (H := H)),
      dotProduct (g y).val (primalValues (F.forward e) z v) = 0) :
    componentResponse F e z D E S T (δ + f) (ε + g) =
      componentResponse F e z D E S T δ ε

axiom nonlinear_component_correction {Comp B H : Type} [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T)
    (β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary)
    {K R : ℕ} (hS : Module.finrank Binary S ≤ K) (hT : Module.finrank Binary T ≤ K)
    (hplus : Module.finrank Binary (LinearMap.range ((F.forward e).compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R)
    (hminus : Module.finrank Binary (LinearMap.range ((F.reverse e).flip.compl₁₂
      (primal (B := B) (H := H)).subtype (channelEmbedding z))) ≤ R)
    (hδ : Module.finrank Binary (LinearMap.range δ) ≤ R)
    (hε : Module.finrank Binary (LinearMap.range ε) ≤ R)
    (hcapacity : Module.finrank Binary (LinearMap.range β) + 2 * K + 4 * R ≤ Fintype.card H) :
    ∃ δ' ε', componentResponse F e z D E S T δ' ε' = componentResponse F e z D E S T δ ε ∧
      extraProduct D E S T δ' ε' = β + extraProduct D E S T δ ε

axiom paper_channel_capacity {r J components Dquo K R h rank : ℕ}
    (hrank : rank ≤ 30 * r + 28 * J * components + Dquo)
    (hmargin : 28 * J * components + Dquo + 2 * K + 4 * R < 970 * r)
    (hchannels : 1000 * r ≤ h) : rank + 2 * K + 4 * R ≤ h

axiom ambient_add_expansion {B H : Type} [Fintype B] [Fintype H]
    (f g df dg : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient (f + df) (g + dg) =
      Lax342547.TensorContractions.ambient f g + Lax342547.TensorContractions.ambient f dg +
      Lax342547.TensorContractions.ambient df g + Lax342547.TensorContractions.ambient df dg

end Lax342547.NonlinearChannels
