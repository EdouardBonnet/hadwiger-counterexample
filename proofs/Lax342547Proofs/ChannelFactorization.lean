import Lax342547.ChannelFactorization
import Lax342547Proofs.CompressedResidual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Projective

namespace Lax342547Proofs.ChannelFactorization

open Lax342547.ChannelFactorization

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.ChannelChanges

/--
---
conclusion: Lax342547.ChannelFactorization.factor_through_pairing
---
-/
theorem factor_through_pairing {X Y U V : Type}
    [AddCommGroup X] [Module Binary X] [AddCommGroup Y] [Module Binary Y]
    [AddCommGroup U] [Module Binary U] [AddCommGroup V] [Module Binary V]
    [FiniteDimensional Binary Y] [FiniteDimensional Binary V]
    (β : X →ₗ[Binary] Y →ₗ[Binary] Binary) (π : U →ₗ[Binary] V →ₗ[Binary] Binary)
    (hr : Module.finrank Binary (LinearMap.range β) ≤ Module.finrank Binary (LinearMap.range π)) :
    ∃ f : X →ₗ[Binary] U, ∃ g : Y →ₗ[Binary] V, π.compl₁₂ f g = β := by
  obtain ⟨j, hj⟩ := finrank_le_iff_exists_linearMap.mp hr
  have : Module.Free Binary (LinearMap.range π) := Module.Free.of_divisionRing Binary _
  obtain ⟨t, ht⟩ := π.rangeRestrict.exists_rightInverse_of_surjective π.range_rangeRestrict
  let q : LinearMap.range β →ₗ[Binary] V →ₗ[Binary] Binary :=
    (LinearMap.range π).subtype.comp j
  have hq : Function.Injective q := (LinearMap.range π).injective_subtype.comp hj
  have hsurj : Function.Surjective q.flip := LinearMap.flip_surjective_iff₁.mpr hq
  obtain ⟨s, hs⟩ := q.flip.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  let f := t.comp (j.comp β.rangeRestrict)
  let g := s.comp (LinearMap.range β).subtype.flip
  refine ⟨f, g, ?_⟩
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change π (t (j (β.rangeRestrict x))) (s ((LinearMap.range β).subtype.flip y)) = β x y
  have htv := congrArg Subtype.val (DFunLike.congr_fun ht (j (β.rangeRestrict x)))
  change π (t (j (β.rangeRestrict x))) = (j (β.rangeRestrict x)).val at htv
  rw [htv]
  exact DFunLike.congr_fun (DFunLike.congr_fun hs ((LinearMap.range β).subtype.flip y))
    (β.rangeRestrict x)

/--
---
conclusion: Lax342547.ChannelFactorization.factor_in_channel_spaces
---
-/
theorem factor_in_channel_spaces {X Y H : Type} [Fintype H]
    [AddCommGroup X] [Module Binary X] [AddCommGroup Y] [Module Binary Y]
    [FiniteDimensional Binary Y]
    (S T : Submodule Binary (H → Binary)) (β : X →ₗ[Binary] Y →ₗ[Binary] Binary)
    (hr : Module.finrank Binary (LinearMap.range β) ≤ Module.finrank Binary
      (LinearMap.range ((dotProductBilin Binary Binary).compl₁₂ S.subtype T.subtype))) :
    ∃ f : X →ₗ[Binary] S, ∃ g : Y →ₗ[Binary] T,
      (dotProductBilin Binary Binary).compl₁₂ (S.subtype.comp f) (T.subtype.comp g) = β := by
  exact factor_through_pairing β ((dotProductBilin Binary Binary).compl₁₂ S.subtype T.subtype) hr

/--
---
conclusion: Lax342547.ChannelFactorization.perpendicular_dimension
---
-/
theorem perpendicular_dimension {H : Type} [Fintype H] (S : Submodule Binary (H → Binary)) :
    Module.finrank Binary S + Module.finrank Binary (perpendicular S) = Fintype.card H := by
  classical
  let dot : LinearMap.BilinForm Binary (H → Binary) := dotProductBilin Binary Binary
  have hk : LinearMap.ker dot = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro v w h
    ext a
    have he := DFunLike.congr_fun h (Pi.single a 1)
    change dotProduct v (Pi.single a 1) = dotProduct w (Pi.single a 1) at he
    simpa using he
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := dot) S
  rw [hk, inf_bot_eq, finrank_bot, add_zero] at h
  simpa only [dot, perpendicular, Module.finrank_pi] using h

/--
---
conclusion: Lax342547.ChannelFactorization.channel_pairing_rank
---
-/
theorem channel_pairing_rank {H : Type} [Fintype H]
    (S T : Submodule Binary (H → Binary)) {cS cT : ℕ}
    (hS : Fintype.card H ≤ Module.finrank Binary S + cS)
    (hT : Fintype.card H ≤ Module.finrank Binary T + cT) :
    Fintype.card H ≤ Module.finrank Binary
      (LinearMap.range ((dotProductBilin Binary Binary).compl₁₂ S.subtype T.subtype)) + cS + cT := by
  let π := (dotProductBilin Binary Binary).compl₁₂ S.subtype T.subtype
  let f : LinearMap.ker π →ₗ[Binary] perpendicular T :=
    { toFun := fun v => ⟨v.val.val, by
        change ∀ t ∈ T, dotProduct t v.val.val = 0
        intro t ht
        have h := DFunLike.congr_fun (LinearMap.mem_ker.mp v.property) (⟨t, ht⟩ : T)
        change dotProduct v.val.val t = 0 at h
        simpa only [dotProduct_comm] using h⟩
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : perpendicular T => z.val) h
  have hr := LinearMap.finrank_le_finrank_of_injective hf
  have hn := π.finrank_range_add_finrank_ker
  have hp := perpendicular_dimension T
  dsimp only [π] at hn hr
  omega

/--
---
conclusion: Lax342547.ChannelFactorization.remaining_values_dimension
---
-/
theorem remaining_values_dimension {A B H : Type} [Fintype H]
    [AddCommGroup A] [Module Binary A] [AddCommGroup B] [Module Binary B]
    (S : Submodule Binary (H → Binary)) (G : A →ₗ[Binary] (H → Binary))
    (D : B →ₗ[Binary] (H → Binary)) {K R : ℕ}
    (hS : Module.finrank Binary S ≤ K)
    (hG : Module.finrank Binary (LinearMap.range G) ≤ R)
    (hD : Module.finrank Binary (LinearMap.range D) ≤ R) :
    Fintype.card H ≤ Module.finrank Binary (remainingValues S G D) + (K + 2 * R) := by
  have hsup := (Submodule.finrank_add_le_finrank_add_finrank (S ⊔ LinearMap.range G)
    (LinearMap.range D)).trans (Nat.add_le_add_right
      (Submodule.finrank_add_le_finrank_add_finrank S (LinearMap.range G)) _)
  have hp := perpendicular_dimension (S ⊔ LinearMap.range G ⊔ LinearMap.range D)
  change Fintype.card H ≤ Module.finrank Binary
    (perpendicular (S ⊔ LinearMap.range G ⊔ LinearMap.range D)) + (K + 2 * R)
  omega

/--
---
conclusion: Lax342547.ChannelFactorization.remaining_values_allowed
---
-/
theorem remaining_values_allowed {A B H : Type} [Fintype H]
    [AddCommGroup A] [Module Binary A] [AddCommGroup B] [Module Binary B]
    (S : Submodule Binary (H → Binary)) (G : A →ₗ[Binary] (H → Binary))
    (D : B →ₗ[Binary] (H → Binary)) : remainingValues S G D ≤ perpendicular S := by
  intro v hv
  change ∀ w ∈ S, dotProduct w v = 0
  change ∀ w ∈ S ⊔ LinearMap.range G ⊔ LinearMap.range D, dotProduct w v = 0 at hv
  intro w hw
  exact hv w (Submodule.mem_sup_left (Submodule.mem_sup_left hw))

/--
---
conclusion: Lax342547.ChannelFactorization.remaining_values_orthogonal
---
-/
theorem remaining_values_orthogonal {A B H : Type} [Fintype H]
    [AddCommGroup A] [Module Binary A] [AddCommGroup B] [Module Binary B]
    (S : Submodule Binary (H → Binary)) (G : A →ₗ[Binary] (H → Binary))
    (D : B →ₗ[Binary] (H → Binary)) (v : remainingValues S G D) :
    (∀ a, dotProduct v.val (G a) = 0) ∧ (∀ b, dotProduct v.val (D b) = 0) := by
  have hv := v.property
  change ∀ w ∈ S ⊔ LinearMap.range G ⊔ LinearMap.range D, dotProduct w v.val = 0 at hv
  constructor
  · intro a
    rw [dotProduct_comm]
    exact hv _ (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨a, rfl⟩))
  · intro b
    rw [dotProduct_comm]
    exact hv _ (Submodule.mem_sup_right ⟨b, rfl⟩)

/--
---
conclusion: Lax342547.ChannelFactorization.remaining_values_factor
---
-/
theorem remaining_values_factor {X Y A B C D H : Type} [Fintype H]
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
        ((remainingValues S G dG).subtype.comp f) ((remainingValues T F dF).subtype.comp g) = β := by
  have hleft := remaining_values_dimension S G dG hS hG hdG
  have hright := remaining_values_dimension T F dF hT hF hdF
  have hr := channel_pairing_rank _ _ hleft hright
  apply factor_in_channel_spaces
  omega

open Lax342547.PairedAnnihilators Lax342547.ResponseMatrices

/--
---
conclusion: Lax342547.ChannelFactorization.allowed_pure_factor
---
-/
theorem allowed_pure_factor {B H A C E F : Type} [Fintype B] [Fintype H]
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
      (∀ y f, dotProduct (ε y).val (dG' f) = 0) := by
  obtain ⟨f, g, he⟩ := remaining_values_factor S T G dG G' dG' β hS hT hG hdG hG' hdG' hcapacity
  let δ := ((remainingValues S G dG).inclusion (remaining_values_allowed S G dG)).comp f
  let ε := ((remainingValues T G' dG').inclusion (remaining_values_allowed T G' dG')).comp g
  refine ⟨δ, ε, he, ?_, ?_, ?_, ?_⟩
  · intro x a
    exact (remaining_values_orthogonal S G dG (f x)).1 a
  · intro x c
    exact (remaining_values_orthogonal S G dG (f x)).2 c
  · intro y e
    exact (remaining_values_orthogonal T G' dG' (g y)).1 e
  · intro y z
    exact (remaining_values_orthogonal T G' dG' (g y)).2 z

end Lax342547Proofs.ChannelFactorization
