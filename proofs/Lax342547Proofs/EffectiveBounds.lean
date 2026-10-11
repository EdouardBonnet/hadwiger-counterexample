import Lax342547.EffectiveBounds
import Lax342547.ProjectedPins

namespace Lax342547Proofs.EffectiveBounds

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins
open scoped TensorProduct

/--
---
conclusion: Lax342547.EffectiveBounds.tensor_dimension
---
Every generating outer product is in the image of the canonical linear
map from S tensor T to matrices. Its range dimension is bounded by the
dimension of the domain, which is the product of the two dimensions.
-/
theorem tensor_dimension {B : Type} [Fintype B] (S T : Submodule Binary (B → Binary)) :
    Module.finrank Binary (tensorSpace S T) ≤ Module.finrank Binary S * Module.finrank Binary T := by
  let : Module.Finite Binary (S ⊗[Binary] T) := Module.Finite.of_basis
    ((Module.finBasis Binary S).tensorProduct (Module.finBasis Binary T))
  let f : S ⊗[Binary] T →ₗ[Binary] Matrix B B Binary :=
    TensorProduct.lift ((vecMulVecBilin Binary Binary).compl₁₂ S.subtype T.subtype)
  have hle : tensorSpace S T ≤ LinearMap.range f := by
    apply Submodule.span_le.mpr
    rintro M ⟨v, hv, w, hw, rfl⟩
    exact ⟨(⟨v, hv⟩ : S) ⊗ₜ[Binary] (⟨w, hw⟩ : T), by simp [f]⟩
  exact (Submodule.finrank_mono hle).trans (f.finrank_range_le.trans_eq Module.finrank_tensorProduct)

theorem tensor_columns {B : Type} (S T : Submodule Binary (B → Binary))
    {M : Matrix B B Binary} (hM : M ∈ tensorSpace S T) : ∀ j, (fun i => M i j) ∈ S := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨v, hv, w, _hw, rfl⟩ := hM
    intro j
    convert S.smul_mem (w j) hv using 1
    ext i
    simp [Matrix.vecMulVec, mul_comm]
  | zero => exact fun _ => S.zero_mem
  | add M M' _ _ hM hM' => exact fun j => S.add_mem (hM j) (hM' j)
  | smul c M _ hM => exact fun j => S.smul_mem c (hM j)

theorem tensor_transpose {B : Type} (S T : Submodule Binary (B → Binary))
    {M : Matrix B B Binary} (hM : M ∈ tensorSpace S T) : M.transpose ∈ tensorSpace T S := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨v, hv, w, hw, rfl⟩ := hM
    apply Submodule.subset_span
    exact ⟨w, hw, v, hv, by ext i j; simp [Matrix.vecMulVec, mul_comm]⟩
  | zero => exact (tensorSpace T S).zero_mem
  | add M M' _ _ hM hM' => exact (tensorSpace T S).add_mem hM hM'
  | smul c M _ hM => exact (tensorSpace T S).smul_mem c hM

theorem tensor_rank_left {B : Type} [Fintype B] (S T : Submodule Binary (B → Binary))
    (M : Matrix B B Binary) (hM : M ∈ tensorSpace S T) : M.rank ≤ Module.finrank Binary S := by
  have hcol := tensor_columns S T hM
  have hrange : LinearMap.range M.mulVecLin ≤ S := by
    rintro _ ⟨v, rfl⟩
    have he : M.mulVecLin v = ∑ j, v j • (fun i => M i j) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [he]
    exact S.sum_mem (fun j _ => S.smul_mem (v j) (hcol j))
  exact Submodule.finrank_mono hrange

/--
---
conclusion: Lax342547.EffectiveBounds.tensor_rank
---
The range of every tensor matrix is contained in its first factor space.
Apply the same argument to the transpose to bound the rank by the second
factor as well.
-/
theorem tensor_rank {B : Type} [Fintype B] (S T : Submodule Binary (B → Binary))
    (M : Matrix B B Binary) (hM : M ∈ tensorSpace S T) :
    M.rank ≤ min (Module.finrank Binary S) (Module.finrank Binary T) := by
  refine le_min (tensor_rank_left S T M hM) ?_
  simpa only [Matrix.rank_transpose] using tensor_rank_left T S M.transpose (tensor_transpose S T hM)

theorem sign_rank {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (s : Bool) :
    (∑ e, Module.finrank Binary (projected P i (e, s))) ≤ P.rank := by
  have h := Lax342547.ProjectedPins.projected_rank P i
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib] at h
  cases s <;> omega

def componentMap {Comp B H N : Type} (X : Submodule Binary (Comp → Matrix B B Binary))
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) :
    effective X P i →ₗ[Binary] ∀ e, tensorSpace (projected P i (e, true)) (projected P i (e, false)) where
  toFun x e := ⟨x.val.val e, x.property e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem componentMap_injective {Comp B H N : Type}
    (X : Submodule Binary (Comp → Matrix B B Binary))
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) :
    Function.Injective (componentMap X P i) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  ext e a b
  exact congrArg (fun f => (f e).val a b) h

/--
---
conclusion: Lax342547.EffectiveBounds.effective_bounds
---
Embed the effective space into the product of its component tensor spaces.
Their dimensions sum to at most the product of the total projected plus
and minus dimensions. Each total is bounded by K. Component matrix ranks
are bounded by the plus projection dimensions, whose sum is at most K.
-/
theorem effective_bounds {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (X : Submodule Binary (Comp → Matrix B B Binary))
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (K : ℕ) (hK : P.rank ≤ K) :
    Module.finrank Binary (effective X P i) ≤ K ^ 2 ∧
      ∀ x ∈ effective X P i, (∑ e, (x.val e).rank) ≤ K := by
  classical
  have hplus : (∑ e, Module.finrank Binary (projected P i (e, true))) ≤ K :=
    (sign_rank P i true).trans hK
  have hminus : (∑ e, Module.finrank Binary (projected P i (e, false))) ≤ K :=
    (sign_rank P i false).trans hK
  constructor
  · calc
      _ ≤ Module.finrank Binary
          (∀ e, tensorSpace (projected P i (e, true)) (projected P i (e, false))) :=
        LinearMap.finrank_le_finrank_of_injective (componentMap_injective X P i)
      _ = ∑ e, Module.finrank Binary
          (tensorSpace (projected P i (e, true)) (projected P i (e, false))) :=
        Module.finrank_pi_fintype _
      _ ≤ ∑ e, Module.finrank Binary (projected P i (e, true)) *
          Module.finrank Binary (projected P i (e, false)) :=
        Finset.sum_le_sum (fun e _ => Lax342547.EffectiveBounds.tensor_dimension _ _)
      _ ≤ ∑ e, Module.finrank Binary (projected P i (e, true)) * K := by
        apply Finset.sum_le_sum
        intro e _
        apply Nat.mul_le_mul_left
        exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)).trans hminus
      _ = (∑ e, Module.finrank Binary (projected P i (e, true))) * K :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ K * K := Nat.mul_le_mul_right K hplus
      _ = K ^ 2 := (pow_two K).symm
  · intro x hx
    exact (Finset.sum_le_sum (fun e _ => tensor_rank_left _ _ (x.val e) (hx e))).trans hplus

end Lax342547Proofs.EffectiveBounds
