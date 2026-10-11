import Lax342547.RankedProjection
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
---
title: Small affine slices force global cross-coefficient rank
type: lemma
---
Every matrix rank has a witness on actual coordinate rows and columns. A sum
of s affine products has a cross-coefficient matrix of rank at most 2s.
The same bound on every (2s+1)-square coordinate slice forces the global
bound. Summed predictor parity then contradicts an identity matrix larger
than the sum of these ranks. This is the deterministic conclusion of Lemma 9.5.
-/

namespace Lax342547.SmallSliceRank
open Lax342547.MomentSpace
open scoped BigOperators

axiom independent_column_selection {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J Binary) (t : ℕ) (ht : t ≤ A.rank) :
    ∃ c : Fin t → J,Function.Injective c ∧ (A.submatrix id c).rank = t

axiom rank_witness {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J Binary) (t : ℕ) (ht : t ≤ A.rank) :
    ∃ r : Fin t → I,∃ c : Fin t → J,
      Function.Injective r ∧ Function.Injective c ∧ (A.submatrix r c).rank = t

axiom rank_le_of_small_slices {I J : Type} [Fintype I] [Fintype J]
    (A : Matrix I J Binary) (r : ℕ)
    (h : ∀ i : Fin (r+1) → I,∀ j : Fin (r+1) → J,
      Function.Injective i → Function.Injective j → (A.submatrix i j).rank ≤ r) : A.rank ≤ r

def crossCoefficients {I J : Type} [DecidableEq I] [DecidableEq J]
    (F : (I → Binary) → (J → Binary) → Binary) : Matrix I J Binary :=
    fun i j => F (Pi.single i 1) (Pi.single j 1)+F (Pi.single i 1) 0+
      F 0 (Pi.single j 1)+F 0 0

def affineValue {I J : Type} [Fintype I] [Fintype J]
    (c : Binary) (a : I → Binary) (b : J → Binary) (x : I → Binary) (y : J → Binary) : Binary :=
    c+dotProduct a x+dotProduct b y

axiom cross_affine_product {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (c d : Binary) (a u : I → Binary) (b v : J → Binary) :
    crossCoefficients (fun x y => affineValue c a b x y*affineValue d u v x y) =
      Matrix.vecMulVec a v+Matrix.vecMulVec u b

axiom cross_products_rank {P I J : Type} [Fintype P] [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (c d : P → Binary) (a u : P → I → Binary)
    (b v : P → J → Binary) :
    (crossCoefficients (fun x y => ∑ p,affineValue (c p) (a p) (b p) x y*
      affineValue (d p) (u p) (v p) x y)).rank ≤ 2*Fintype.card P

def liftCoordinates {T I : Type} [Fintype T] [DecidableEq I]
    (r : T → I) (x : T → Binary) : I → Binary := ∑ t,x t • Pi.single (r t) 1

def HasProducts {I J : Type} [Fintype I] [Fintype J]
    (s : ℕ) (F : (I → Binary) → (J → Binary) → Binary) : Prop :=
    ∃ c d : Fin s → Binary,∃ a u : Fin s → I → Binary,∃ b v : Fin s → J → Binary,
      ∀ x y,F x y = ∑ p,affineValue (c p) (a p) (b p) x y*affineValue (d p) (u p) (v p) x y

axiom cross_rank_of_products {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (s : ℕ) (F : (I → Binary) → (J → Binary) → Binary)
    (h : HasProducts s F) : (crossCoefficients F).rank ≤ 2*s

axiom rank_from_local_products {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (s : ℕ) (F : (I → Binary) → (J → Binary) → Binary)
    (h : ∀ r : Fin (2*s+1) → I,∀ c : Fin (2*s+1) → J,
      Function.Injective r → Function.Injective c →
      HasProducts s (fun x y => F (liftCoordinates r x) (liftCoordinates c y))) :
    (crossCoefficients F).rank ≤ 2*s

axiom parity_rank_contradiction {T : Type} [Fintype T] (s m : ℕ)
    (F : T → (Fin m → Binary) → (Fin m → Binary) → Binary)
    (hparity : ∀ x y,(∑ l,F l x y) = dotProduct x y)
    (hloc : ∀ l : T,∀ r : Fin (2*s+1) → Fin m,∀ c : Fin (2*s+1) → Fin m,
      Function.Injective r → Function.Injective c →
      HasProducts s (fun x y => F l (liftCoordinates r x) (liftCoordinates c y)))
    (hm : 2*s*Fintype.card T < m) : False

end Lax342547.SmallSliceRank
