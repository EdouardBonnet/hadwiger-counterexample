import Lax342547.ExactPins
import Mathlib.Data.Matrix.Mul

/-!
---
title: Primal projections and preservation of effective spaces
type: definition and theorem
---
Pins can mix endpoints and channels. Their endpoint primal spaces are
therefore projections. Enlarging pins preserves these spaces and the
cut profiles supported in their tensor products.
-/

namespace Lax342547.ProjectedPins

open Lax342547.MomentSpace Lax342547.ExactPins

def primalProjection {B H : Type} (i : Fin 2) :
    ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (B → Binary) where
  toFun v b := v (i, Sum.inl b)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def projected {Comp B H N : Type} (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (i : Fin 2) (a : Comp × Bool) : Submodule Binary (B → Binary) :=
  (P.space a).map (primalProjection i)

def tensorSpace {B : Type} (S T : Submodule Binary (B → Binary)) :
    Submodule Binary (Matrix B B Binary) :=
  Submodule.span Binary {M | ∃ v ∈ S, ∃ w ∈ T, M = Matrix.vecMulVec v w}

def effective {Comp B H N : Type} (X : Submodule Binary (Comp → Matrix B B Binary))
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) : Submodule Binary X where
  carrier := {x | ∀ e, x.val e ∈ tensorSpace (projected P i (e, true)) (projected P i (e, false))}
  zero_mem' := fun _e => (tensorSpace _ _).zero_mem
  add_mem' := fun hx hy e => (tensorSpace _ _).add_mem (hx e) (hy e)
  smul_mem' := fun c _ hx e => (tensorSpace _ _).smul_mem c (hx e)

axiom projected_rank {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) :
    (∑ a, Module.finrank Binary (projected P i a)) ≤ P.rank

axiom projected_mono {Comp B H N : Type}
    (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (h : P.Extends Q) (i : Fin 2) :
    ∀ a, projected P i a ≤ projected Q i a

axiom effective_mono {Comp B H N : Type} (X : Submodule Binary (Comp → Matrix B B Binary))
    (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (h : P.Extends Q) (i : Fin 2) :
    effective X P i ≤ effective X Q i

end Lax342547.ProjectedPins
