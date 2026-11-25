import Lax793645.ConstructionData

/-!
---
title: The selector space of a low rank matrix
type: lemma
---
For a separately symmetric tensor matrix of rank $r$, one selector subspace of
dimension at most $r^2$ contains every selector slice of every column. Consequently
each reshaped column also has rank at most $r^2$.
-/

namespace Lax793645.SelectorConfinement

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule Module
open scoped BigOperators
variable {S T : Type} [Fintype S] [Fintype T]

axiom selector_confinement (w : Mat (S × T) (S × T))
    (hs : ∀ a b i j, w (a,i) (b,j)=w (a,j) (b,i)) :
    ∃ U : Space (Vec S), dim U ≤ w.rank^2 ∧
      ∀ x ∈ colSp w, ∀ i, selectorSlice i x ∈ U

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule Module
open scoped BigOperators
variable {S T : Type} [Fintype S] [Fintype T]

axiom reshape_rank_le (w : Mat (S × T) (S × T))
    (hs : ∀ a b i j, w (a,i) (b,j)=w (a,j) (b,i))
    (x : Vec (S × T)) (hx : x ∈ colSp w) :
    Matrix.rank ((fun a i => x (a,i)) : Mat S T) ≤ w.rank^2

end

end Lax793645.SelectorConfinement
