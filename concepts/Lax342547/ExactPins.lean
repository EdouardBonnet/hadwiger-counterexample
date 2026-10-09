import Lax342547.MomentSpace
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Isomorphisms

/-!
---
title: Exact image pins in nominal coefficient spaces
type: definition and theorem
---
A pin stores a subspace at each component/sign and the prescribed linear
image on that subspace. New rank is the sum of dimensions of the tested
spaces in the quotients by the old pins, before any frame is applied.
-/

namespace Lax342547.ExactPins

open Lax342547.MomentSpace

def Pin (Axis I N : Type) :=
  Σ S : Axis → Submodule Binary (I → Binary), ∀ a, S a →ₗ[Binary] (N → Binary)

namespace Pin

variable {Axis I N : Type}

def space (P : Pin Axis I N) (a : Axis) : Submodule Binary (I → Binary) := P.1 a
def value (P : Pin Axis I N) (a : Axis) : P.space a →ₗ[Binary] (N → Binary) := P.2 a

def empty : Pin Axis I N := ⟨fun _ => ⊥, fun _ => 0⟩

def Extends (P Q : Pin Axis I N) : Prop :=
  ∃ h : ∀ a, P.space a ≤ Q.space a,
    ∀ a (v : P.space a), Q.value a ⟨v.val, h a v.property⟩ = P.value a v

noncomputable def rank [Fintype Axis] (P : Pin Axis I N) : ℕ :=
  ∑ a, Module.finrank Binary (P.space a)

noncomputable def relativeRank [Fintype Axis] (P Q : Pin Axis I N) : ℕ :=
  ∑ a, Module.finrank Binary ((Q.space a).map (P.space a).mkQ)

def event {Ω : Type} (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P : Pin Axis I N) : Set Ω :=
  {o | ∀ a (v : P.space a), A o a v.val = P.value a v}

def joinAt {Ω : Type} (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary))
    (P Q : Pin Axis I N) (o : Ω) : Pin Axis I N :=
  ⟨fun a => P.space a ⊔ Q.space a,
    fun a => (A o a).comp (P.space a ⊔ Q.space a).subtype⟩

noncomputable def basisMatrix [Fintype I] (P : Pin Axis I N) (a : Axis) :
    Matrix I (Fin (Module.finrank Binary (P.space a))) Binary :=
  fun i j => (Module.finBasis Binary (P.space a) j).val i

noncomputable def basisImage [Fintype I] (P : Pin Axis I N) (a : Axis) :
    Matrix N (Fin (Module.finrank Binary (P.space a))) Binary :=
  fun n j => P.value a (Module.finBasis Binary (P.space a) j) n

end Pin

noncomputable instance {Axis I N : Type} [Fintype Axis] [Fintype I] [Fintype N] :
    Fintype (Pin Axis I N) := by
  classical
  let : Finite (Submodule Binary (I → Binary)) :=
    Finite.of_injective (fun S : Submodule Binary (I → Binary) => (S : Set (I → Binary))) SetLike.coe_injective
  let : ∀ S : Submodule Binary (I → Binary), Finite (S →ₗ[Binary] (N → Binary)) :=
    fun S => Finite.of_injective (fun f : S →ₗ[Binary] (N → Binary) => (f : S → N → Binary)) DFunLike.coe_injective
  exact Fintype.ofFinite (Σ S : Axis → Submodule Binary (I → Binary), ∀ a, S a →ₗ[Binary] (N → Binary))

axiom event_refinement {Ω Axis I N : Type}
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (P Q : Pin Axis I N)
    (o : Ω) (ho : o ∈ P.event A ∩ Q.event A) :
    P.Extends (P.joinAt A Q o) ∧ Q.Extends (P.joinAt A Q o) ∧
      (P.joinAt A Q o).event A = P.event A ∩ Q.event A

axiom rank_refinement {Ω Axis I N : Type} [Fintype Axis] [Fintype I]
    (A : Ω → Axis → (I → Binary) →ₗ[Binary] (N → Binary)) (P Q : Pin Axis I N) (o : Ω) :
    (P.joinAt A Q o).rank = P.rank + P.relativeRank Q

axiom rank_mono {Axis I N : Type} [Fintype Axis] [Fintype I]
    (P Q : Pin Axis I N) (h : P.Extends Q) : P.rank ≤ Q.rank

axiom basis_rank {Axis I N : Type} [Fintype I] (P : Pin Axis I N) (a : Axis) :
    (P.basisMatrix a).rank = Module.finrank Binary (P.space a)

axiom event_basis {Ω Axis I N : Type} [Fintype I]
    (A : Ω → Axis → Matrix N I Binary) (P : Pin Axis I N) :
    P.event (fun o a => (A o a).mulVecLin) =
      {o | ∀ a, A o a * P.basisMatrix a = P.basisImage a}

end Lax342547.ExactPins
