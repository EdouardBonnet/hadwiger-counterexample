import Lax342547.ExactPins
import Lean.Elab.Tactic.Omega

namespace Lax342547Proofs.ExactPins

open Lax342547.MomentSpace Lax342547.ExactPins

variable {Ω Axis I N : Type}

theorem extends_refl (P : Pin Axis I N) : P.Extends P := ⟨fun _ => le_rfl, fun _ _ => rfl⟩

theorem extends_trans {P Q R : Pin Axis I N} (hPQ : P.Extends Q) (hQR : Q.Extends R) :
    P.Extends R := by
  obtain ⟨hPQ, hvPQ⟩ := hPQ
  obtain ⟨hQR, hvQR⟩ := hQR
  refine ⟨fun a => (hPQ a).trans (hQR a), fun a v => ?_⟩
  exact (hvQR a ⟨v.val, hPQ a v.property⟩).trans (hvPQ a v)

theorem event_mono (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    {P Q : Pin Axis I N} (hPQ : P.Extends Q) : Q.event A ⊆ P.event A := by
  obtain ⟨hPQ, hvPQ⟩ := hPQ
  intro o ho a v
  exact (ho a ⟨v.val, hPQ a v.property⟩).trans (hvPQ a v)

theorem empty_event (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) :
    (Pin.empty : Pin Axis I N).event A = Set.univ := by
  ext o
  simp only [Pin.event, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro a v
  have hv : v.val = 0 := v.property
  change A o a v.val = 0
  rw [hv, map_zero]

theorem empty_extends (P : Pin Axis I N) : (Pin.empty : Pin Axis I N).Extends P := by
  let h : ∀ a, (Pin.empty : Pin Axis I N).space a ≤ P.space a := fun _ => bot_le
  refine ⟨h, fun a v => ?_⟩
  have hv : v.val = 0 := v.property
  have hz : (⟨v.val, h a v.property⟩ : P.space a) = 0 := Subtype.ext hv
  change P.value a ⟨v.val, h a v.property⟩ = 0
  rw [hz, map_zero]

@[simp] theorem empty_rank [Fintype Axis] : (Pin.empty : Pin Axis I N).rank = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  change Module.finrank Binary (⊥ : Submodule Binary (I → Binary)) = 0
  exact finrank_bot Binary (I → Binary)

/--
---
conclusion: Lax342547.ExactPins.event_refinement
---
A surviving anchor supplies the prescribed images on the sum of the
old and tested spaces. Linearity makes the resulting event exactly the
intersection, while preserving every previously pinned image.
-/
theorem event_refinement
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (P Q : Pin Axis I N)
    (o : Ω) (ho : o ∈ P.event A ∩ Q.event A) :
    P.Extends (P.joinAt A Q o) ∧ Q.Extends (P.joinAt A Q o) ∧
      (P.joinAt A Q o).event A = P.event A ∩ Q.event A := by
  have hP : P.Extends (P.joinAt A Q o) :=
    ⟨fun _ => le_sup_left, fun a v => ho.1 a v⟩
  have hQ : Q.Extends (P.joinAt A Q o) :=
    ⟨fun _ => le_sup_right, fun a v => ho.2 a v⟩
  refine ⟨hP, hQ, Set.Subset.antisymm ?_ ?_⟩
  · exact fun _ hx => ⟨event_mono A hP hx, event_mono A hQ hx⟩
  · intro x hx a v
    change A x a v.val = A o a v.val
    obtain ⟨u, hu, w, hw, he⟩ := Submodule.mem_sup.mp v.property
    rw [← he, map_add, map_add]
    exact congrArg₂ (· + ·) ((hx.1 a ⟨u, hu⟩).trans (ho.1 a ⟨u, hu⟩).symm)
      ((hx.2 a ⟨w, hw⟩).trans (ho.2 a ⟨w, hw⟩).symm)

theorem quotient_increment [Fintype I] (S T : Submodule Binary (I → Binary)) :
    Module.finrank Binary ↥(S ⊔ T) = Module.finrank Binary S + Module.finrank Binary (T.map S.mkQ) := by
  have hS := S.finrank_quotient_add_finrank
  have hT := (T.map S.mkQ).finrank_quotient_add_finrank
  have hST := (S ⊔ T).finrank_quotient_add_finrank
  have he := (Submodule.quotientQuotientEquivQuotientSup S T).finrank_eq
  omega

/--
---
conclusion: Lax342547.ExactPins.rank_refinement
---
The third isomorphism theorem and rank-nullity identify the increase in
each stored pin dimension with the tested span's dimension in the old
nominal quotient. Summing gives the exact rank increment.
-/
theorem rank_refinement [Fintype Axis] [Fintype I]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (P Q : Pin Axis I N) (o : Ω) :
    (P.joinAt A Q o).rank = P.rank + P.relativeRank Q := by
  change (∑ a, Module.finrank Binary ↥(P.space a ⊔ Q.space a)) = _
  simp only [quotient_increment, Finset.sum_add_distrib, Pin.rank, Pin.relativeRank]

/--
---
conclusion: Lax342547.ExactPins.rank_mono
---
An extension contains every old nominal pin space, so its total dimension
cannot decrease.
-/
theorem rank_mono [Fintype Axis] [Fintype I]
    (P Q : Pin Axis I N) (h : P.Extends Q) : P.rank ≤ Q.rank := by
  obtain ⟨h, _⟩ := h
  exact Finset.sum_le_sum (fun a _ => Submodule.finrank_mono (h a))

theorem basis_injective [Fintype I] (P : Pin Axis I N) (a : Axis) :
    Function.Injective (P.basisMatrix a).mulVec := by
  classical
  apply Matrix.mulVec_injective_iff.mpr
  exact (Module.finBasis Binary (P.space a)).linearIndependent.map' (P.space a).subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)

/--
---
conclusion: Lax342547.ExactPins.basis_rank
---
The columns are an actual basis of the stored nominal subspace, included
in its coefficient space. They are independent and have precisely the
stored dimension.
-/
theorem basis_rank [Fintype I] (P : Pin Axis I N) (a : Axis) :
    (P.basisMatrix a).rank = Module.finrank Binary (P.space a) := by
  rw [Matrix.rank, LinearMap.finrank_range_of_inj (basis_injective P a),
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/--
---
conclusion: Lax342547.ExactPins.event_basis
---
Equality of two linear maps on every stored basis vector is equivalent
to equality throughout the pin space. The matrix event therefore keeps
exactly the same information as the prescribed linear images.
-/
theorem event_basis [Fintype I]
    (A : Ω → Axis → Matrix N I Binary) (P : Pin Axis I N) :
    P.event (fun o a => (A o a).mulVecLin) =
      {o | ∀ a, A o a * P.basisMatrix a = P.basisImage a} := by
  ext o
  constructor
  · intro ho a
    ext n j
    exact congrFun (ho a (Module.finBasis Binary (P.space a) j)) n
  · intro ho a v
    let f := (A o a).mulVecLin.comp (P.space a).subtype
    have hf : f = P.value a := (Module.finBasis Binary (P.space a)).ext (by
      intro j
      funext n
      exact congrArg (fun M => M n j) (ho a))
    exact congrArg (fun f : P.space a →ₗ[Binary] (N → Binary) => f v) hf

end Lax342547Proofs.ExactPins
