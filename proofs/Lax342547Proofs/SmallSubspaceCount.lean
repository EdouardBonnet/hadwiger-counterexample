import Lax342547.SmallSubspaceCount
import Lax342547Proofs.FiniteLinearLaw
import Mathlib.LinearAlgebra.Basis.VectorSpace

namespace Lax342547Proofs.SmallSubspaceCount
open Lax342547.SmallSubspaceCount

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace

/--
---
conclusion: Lax342547.SmallSubspaceCount.padded_generators
---
-/
theorem padded_generators {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Submodule K V) (r : ℕ) (hr : Module.finrank K S ≤ r) :
    ∃ f : Fin r → V, Submodule.span K (Set.range f) = S := by
  classical
  let b := Module.finBasis K S
  let f : Fin r → V := fun i => if h : i.val < Module.finrank K S then (b ⟨i.val,h⟩).val else 0
  refine ⟨f,le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    dsimp [f]
    split_ifs
    · exact (b _).property
    · exact S.zero_mem
  · intro v hv
    let u : S := ⟨v,hv⟩
    have hb := b.sum_repr u
    have he : ∑ i, (b.repr u i) • (b i).val = v := by
      simpa only [Submodule.coe_sum,Submodule.coe_smul,u] using congrArg (fun z : S => z.val) hb
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    have hm : (b i).val ∈ Set.range f := by
      refine ⟨⟨i.val,lt_of_lt_of_le i.isLt hr⟩,?_⟩
      simp only [f,dif_pos i.isLt]
    exact Submodule.subset_span hm

/--
---
conclusion: Lax342547.SmallSubspaceCount.small_subspace_card
---
-/
theorem small_subspace_card {H : Type} [Fintype H] (r : ℕ) :
    Nat.card {S : Submodule Binary (H → Binary) // Module.finrank Binary S ≤ r} ≤
      2^(Fintype.card H*r) := by
  classical
  let F := fun f : Fin r → (H → Binary) => Submodule.span Binary (Set.range f)
  have hrank (f : Fin r → (H → Binary)) : Module.finrank Binary (F f) ≤ r := by
    simpa only [F,Set.finrank,Fintype.card_fin] using (finrank_range_le_card (R := Binary) f)
  let g : (Fin r → (H → Binary)) → {S : Submodule Binary (H → Binary) // Module.finrank Binary S ≤ r} :=
    fun f => ⟨F f,hrank f⟩
  have hg : Function.Surjective g := by
    intro S
    obtain ⟨f,hf⟩ := padded_generators S.val r S.property
    exact ⟨f,Subtype.ext hf⟩
  have hc := Nat.card_le_card_of_surjective g hg
  have he : Nat.card (Fin r → (H → Binary)) = 2^(Fintype.card H*r) := by
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card,← pow_mul]
  simpa only [he] using hc

end Lax342547Proofs.SmallSubspaceCount
