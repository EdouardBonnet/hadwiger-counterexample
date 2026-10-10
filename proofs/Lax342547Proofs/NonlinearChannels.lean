import Lax342547.NonlinearChannels
import Lax342547Proofs.TargetMatrices

namespace Lax342547Proofs.NonlinearChannels
open Lax342547.NonlinearChannels

set_option backward.isDefEq.respectTransparency false
open Lax342547.ConcreteCut
open Lax342547.MomentSpace Lax342547.PairedAnnihilators Lax342547.ChannelChanges
open Lax342547.ResponseMatrices Lax342547.TableSpaces Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.NominalPrimal Lax342547.TensorAnnihilators

/--
---
conclusion: Lax342547.NonlinearChannels.primal_values_rank
---
-/
theorem primal_values_rank {B H : Type} [Fintype B] [Fintype H]
    (F : LinearMap.BilinForm Binary (Nominal B H)) (z : Fin 2) :
    Module.finrank Binary (LinearMap.range (primalValues F z)) ≤
      Module.finrank Binary (LinearMap.range (F.compl₁₂ primal.subtype (channelEmbedding z))) := by
  classical
  exact Lax342547Proofs.ResponseMatrices.comp_right_rank _ _

/--
---
conclusion: Lax342547.NonlinearChannels.primal_plus_values
---
-/
theorem primal_plus_values {Comp B H : Type} [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (i z : Fin 2) (v : B → Binary) :
    primalValues (F.forward e) z (liftPrimal i v) = fullPlus F e i z v := by
  classical
  rfl

/--
---
conclusion: Lax342547.NonlinearChannels.primal_minus_values
---
-/
theorem primal_minus_values {Comp B H : Type} [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (i z : Fin 2) (v : B → Binary) :
    primalValues (F.reverse e).flip z (liftPrimal i v) = fullMinus F e i z v := by
  classical
  rfl

/--
---
conclusion: Lax342547.NonlinearChannels.extra_product_add
---
-/
theorem extra_product_add {B H : Type} [Fintype H]
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δ f : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε g : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T)
    (hfg : ∀ x y, dotProduct (f x).val (ε y).val = 0)
    (hgf : ∀ x y, dotProduct (g y).val (δ x).val = 0) :
    extraProduct D E S T (δ + f) (ε + g) =
      extraProduct D E S T δ ε + extraProduct D E S T f g := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change dotProduct ((δ x).val + (f x).val) ((ε y).val + (g y).val) =
    dotProduct (δ x).val (ε y).val + dotProduct (f x).val (g y).val
  simp only [dotProduct_add, add_dotProduct, hfg, dotProduct_comm (δ x).val (g y).val,
    hgf, add_zero, zero_add]

/--
---
conclusion: Lax342547.NonlinearChannels.ambient_add_left
---
-/
theorem ambient_add_left {B H : Type} [Fintype B] [Fintype H]
    (f df g : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient (f + df) g =
      Lax342547.TensorContractions.ambient f g + Lax342547.TensorContractions.ambient df g := by
  classical
  have he : (dotProductBilin Binary Binary).compl₁₂ (f + df) g =
      (dotProductBilin Binary Binary).compl₁₂ f g + (dotProductBilin Binary Binary).compl₁₂ df g := by
    ext v w
    exact add_dotProduct _ _ _
  unfold Lax342547.TensorContractions.ambient
  rw [he, map_add]
  exact map_add matrixPairing _ _

/--
---
conclusion: Lax342547.NonlinearChannels.ambient_add_right
---
-/
theorem ambient_add_right {B H : Type} [Fintype B] [Fintype H]
    (f g dg : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient f (g + dg) =
      Lax342547.TensorContractions.ambient f g + Lax342547.TensorContractions.ambient f dg := by
  classical
  have he : (dotProductBilin Binary Binary).compl₁₂ f (g + dg) =
      (dotProductBilin Binary Binary).compl₁₂ f g + (dotProductBilin Binary Binary).compl₁₂ f dg := by
    ext v w
    exact dotProduct_add _ _ _
  unfold Lax342547.TensorContractions.ambient
  rw [he, map_add]
  exact map_add matrixPairing _ _

/--
---
conclusion: Lax342547.NonlinearChannels.ambient_orthogonal_zero
---
-/
theorem ambient_orthogonal_zero {B H : Type} [Fintype B] [Fintype H]
    (f g : (B → Binary) →ₗ[Binary] (H → Binary))
    (h : ∀ v w, dotProduct (f v) (g w) = 0) :
    Lax342547.TensorContractions.ambient f g = 0 := by
  classical
  have he : (dotProductBilin Binary Binary).compl₁₂ f g = 0 := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact h v w
  unfold Lax342547.TensorContractions.ambient
  rw [he, map_zero]
  exact map_zero matrixPairing

/--
---
conclusion: Lax342547.NonlinearChannels.restriction_add
---
-/
theorem restriction_add {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ f : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (i : Fin 2) :
    restriction D S (δ + f) i = restriction D S δ i + restriction D S f i := by
  ext v h
  rfl

/--
---
conclusion: Lax342547.NonlinearChannels.component_response_unchanged
---
-/
theorem component_response_unchanged {Comp B H : Type} [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δ f : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (ε g : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T)
    (hf : ∀ x (v : primal (B := B) (H := H)),
      dotProduct (f x).val (primalValues (F.reverse e).flip z v) = 0)
    (hg : ∀ y (v : primal (B := B) (H := H)),
      dotProduct (g y).val (primalValues (F.forward e) z v) = 0) :
    componentResponse F e z D E S T (δ + f) (ε + g) =
      componentResponse F e z D E S T δ ε := by
  classical
  have hplus (i : Fin 2) : Lax342547.TensorContractions.ambient
      (restriction D S f i) (fullMinus F e i z) = 0 := by
    apply ambient_orthogonal_zero
    intro v w
    exact (primal_minus_values F e i z w) ▸ hf (D.mkQ (primalEmbedding i v)) (liftPrimal i w)
  have hminus (i : Fin 2) : Lax342547.TensorContractions.ambient
      (fullPlus F e i z) (restriction E T g i) = 0 := by
    apply ambient_orthogonal_zero
    intro v w
    rw [dotProduct_comm]
    exact (primal_plus_values F e i z v) ▸ hg (E.mkQ (primalEmbedding i w)) (liftPrimal i v)
  simp only [componentResponse, restriction_add, ambient_add_left, ambient_add_right,
    hplus, hminus, add_zero]



/--
---
conclusion: Lax342547.NonlinearChannels.nonlinear_component_correction
---
-/
theorem nonlinear_component_correction {Comp B H : Type} [Fintype B] [Fintype H]
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
      extraProduct D E S T δ' ε' = β + extraProduct D E S T δ ε := by
  classical
  have hG := (primal_values_rank (F.reverse e).flip z).trans hminus
  have hG' := (primal_values_rank (F.forward e) z).trans hplus
  have hdG := (Lax342547Proofs.ResponseMatrices.comp_right_rank (perpendicular T).subtype ε).trans hε
  have hdG' := (Lax342547Proofs.ResponseMatrices.comp_right_rank (perpendicular S).subtype δ).trans hδ
  obtain ⟨f, g, hfg, hf, hfε, hg, hgδ⟩ := Lax342547Proofs.ChannelFactorization.allowed_pure_factor
    D E S T (primalValues (F.reverse e).flip z) ((perpendicular T).subtype.comp ε)
    (primalValues (F.forward e) z) ((perpendicular S).subtype.comp δ)
    β hS hT hG hdG hG' hdG' hcapacity
  refine ⟨δ + f, ε + g, component_response_unchanged F e z D E S T δ f ε g hf hg, ?_⟩
  rw [extra_product_add D E S T δ f ε g hfε (fun x y => hgδ y x), hfg, add_comm]

/--
---
conclusion: Lax342547.NonlinearChannels.paper_channel_capacity
---
-/
theorem paper_channel_capacity {r J components Dquo K R h rank : ℕ}
    (hrank : rank ≤ 30 * r + 28 * J * components + Dquo)
    (hmargin : 28 * J * components + Dquo + 2 * K + 4 * R < 970 * r)
    (hchannels : 1000 * r ≤ h) : rank + 2 * K + 4 * R ≤ h := by
  omega

/--
---
conclusion: Lax342547.NonlinearChannels.ambient_add_expansion
---
-/
theorem ambient_add_expansion {B H : Type} [Fintype B] [Fintype H]
    (f g df dg : (B → Binary) →ₗ[Binary] (H → Binary)) :
    Lax342547.TensorContractions.ambient (f + df) (g + dg) =
      Lax342547.TensorContractions.ambient f g + Lax342547.TensorContractions.ambient f dg +
      Lax342547.TensorContractions.ambient df g + Lax342547.TensorContractions.ambient df dg := by
  rw [ambient_add_left, ambient_add_right, ambient_add_right]
  abel

end Lax342547Proofs.NonlinearChannels
