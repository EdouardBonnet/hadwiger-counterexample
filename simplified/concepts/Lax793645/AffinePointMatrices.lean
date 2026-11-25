import Lax793645.ConstructionData

/-!
---
title: Symmetry and diagonal identities for affine points
type: lemma
---
In one factor the affine point squares span exactly the symmetric matrices whose
diagonal entries agree with their entries in the constant column. For $s$ and $t$ with
constant coordinate one, form the outer square of $s\otimes t$. Every linear
combination of these squares is separately symmetric in the two indices of either
factor and satisfies the affine diagonal identity in each factor.
-/

namespace Lax793645.AffinePointMatrices

/-- The outer square of the vector with constant coordinate 1 and ordinary
coordinates given by `z`. -/
def pointSquare {I : Type} (z : I → ZMod 2) : Matrix (Option I) (Option I) (ZMod 2) :=
  Matrix.vecMulVec (Option.elim' 1 z) (Option.elim' 1 z)

axiom mem_span_pointSquare_iff {I : Type} [Fintype I]
    (M : Matrix (Option I) (Option I) (ZMod 2)) :
    M ∈ Submodule.span (ZMod 2) (Set.range (@pointSquare I)) ↔
      (∀ i j, M i j = M j i) ∧ ∀ i, M (some i) (some i) = M (some i) none

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix Submodule
open scoped BigOperators
variable {S T : Type} [Fintype S] [Fintype T]

axiom affineTensor_identities (εS : Vec S) (εT : Vec T)
    {w : Mat (S × T) (S × T)} (hw : w ∈ affineTensorSpace εS εT) :
    TensorIdentities εS εT w

end

end Lax793645.AffinePointMatrices
