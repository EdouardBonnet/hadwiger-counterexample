import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Defs

namespace Lax342547Proofs.GramRank

variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype I]

def gram (B : LinearMap.BilinForm K V) (v : I → V) : Matrix I I K :=
  fun i j => B (v i) (v j)

def evalDual (v : I → V) : Module.Dual K V →ₗ[K] (I → K) :=
  LinearMap.pi (fun i => Module.Dual.eval K V (v i))

theorem gram_factor (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (v : I → V) :
    (gram B v).mulVecLin = (evalDual v).comp (LinearMap.comp B (Fintype.linearCombination K v)) := by
  ext x i
  change (∑ j, B (v i) (v j) * x j) = B (∑ j, x j • v j) (v i)
  simp [map_sum, hB.eq, mul_comm]

omit [Fintype I] in
theorem evalDual_injective (v : I → V) (hv : Submodule.span K (Set.range v) = ⊤) :
    Function.Injective (evalDual (K := K) v) := by
  intro f g hfg
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span K (Set.range v) := hv.symm ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact congrFun hfg i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem rank_gram_eq (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (v : I → V) (hv : Submodule.span K (Set.range v) = ⊤) :
    (gram B v).rank = Module.finrank K (LinearMap.range B) := by
  have hf : LinearMap.range (Fintype.linearCombination K v) = ⊤ :=
    (Fintype.range_linearCombination K v).trans hv
  rw [Matrix.rank, gram_factor B hB v, LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top _ hf]
  exact (Submodule.equivMapOfInjective (evalDual v) (evalDual_injective v hv)
    (LinearMap.range B)).finrank_eq.symm

theorem rank_gram_le [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : B.IsSymm) (v : I → V) : (gram B v).rank ≤ Module.finrank K V := by
  rw [Matrix.rank, gram_factor B hB v, LinearMap.range_comp]
  apply (Submodule.finrank_map_le _ _).trans
  rw [LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans (Submodule.finrank_le _)

theorem rank_gram_span (B : LinearMap.BilinForm K V) (hB : B.IsSymm) (v : I → V) :
    (gram B v).rank = Module.finrank K
      (LinearMap.range (B.restrict (Submodule.span K (Set.range v)))) := by
  let U := Submodule.span K (Set.range v)
  have hv (i : I) : v i ∈ U := Submodule.subset_span ⟨i, rfl⟩
  let vU (i : I) : U := ⟨v i, hv i⟩
  have hspan : Submodule.span K (Set.range vU) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff U hv).mpr rfl
  exact rank_gram_eq (B.restrict U) ⟨fun x y => hB.eq x y⟩ vU hspan

theorem rank_gram_le_form [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : B.IsSymm) (v : I → V) :
    (gram B v).rank ≤ Module.finrank K (LinearMap.range B) := by
  rw [Matrix.rank, gram_factor B hB v, LinearMap.range_comp]
  apply (Submodule.finrank_map_le _ _).trans
  exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

theorem restrict_rank_mono [FiniteDimensional K V] (B : LinearMap.BilinForm K V)
    (hB : B.IsSymm) {U W : Submodule K V} (hUW : U ≤ W) :
    Module.finrank K (LinearMap.range (B.restrict U)) ≤
      Module.finrank K (LinearMap.range (B.restrict W)) := by
  let e := Module.finBasis K U
  let v : Fin (Module.finrank K U) → W := fun i => ⟨e i, hUW (e i).property⟩
  have hr := rank_gram_eq (B.restrict U) ⟨fun x y => hB.eq x y⟩ e e.span_eq
  rw [← hr]
  exact rank_gram_le_form (B.restrict W) ⟨fun x y => hB.eq x y⟩ v

end Lax342547Proofs.GramRank
