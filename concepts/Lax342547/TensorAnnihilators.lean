import Lax342547.QuotientRank
import Lax342547.SelectedMoments
import Lax342547.ConcreteGeometry

/-!
---
title: Pure bilinear responses detect quotient tensors
type: lemma
---
Vanishing against every bilinear form on two quotient spaces implies the
component-rank bound used in §6. The selected affine-ray case gives
exactly a scalar point moment, rather than an arbitrary low-rank block.
-/

namespace Lax342547.TensorAnnihilators

open Lax342547.MomentSpace Lax342547.ConcreteGeometry
open Lax342547.BaseMoments Lax342547.SelectedMoments

def dualCoordinates {I : Type} [DecidableEq I] :
    Module.Dual Binary (I → Binary) →ₗ[Binary] (I → Binary) where
  toFun φ i := φ (Pi.single i 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def pureContraction {I : Type} [Fintype I]
    (S T : Submodule Binary (I → Binary))
    (β : ((I → Binary) ⧸ S) →ₗ[Binary] ((I → Binary) ⧸ T) →ₗ[Binary] Binary) :
    Matrix I I Binary →ₗ[Binary] Binary := by
  classical
  exact matrixPair (LinearMap.BilinForm.toMatrix' (β.compl₁₂ S.mkQ T.mkQ))

def PureAnnihilates {I : Type} [Fintype I] (M : Matrix I I Binary)
    (S T : Submodule Binary (I → Binary)) : Prop :=
  ∀ β, pureContraction S T β M = 0

axiom pure_rank {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I Binary) (S T : Submodule Binary (I → Binary))
    (h : PureAnnihilates M S T) :
    M.rank ≤ Module.finrank Binary S + Module.finrank Binary T

axiom pure_sandwich {I P Q : Type} [Fintype I] [Fintype P] [Fintype Q]
    [DecidableEq I] (M : Matrix I I Binary) (S T : Submodule Binary (I → Binary))
    (h : PureAnnihilates M S T) (A : Matrix P I Binary) (B : Matrix Q I Binary)
    (hA : S ≤ LinearMap.ker A.mulVecLin) (hB : T ≤ LinearMap.ker B.mulVecLin) :
    A * M * B.transpose = 0

axiom selected_block {Base : Type} [Fintype Base] [DecidableEq Base]
    (z : Base → Binary) (Z : Matrix (Option Base) (Option Base) Binary)
    (hZ : IsBaseMoment Z)
    (h : PureAnnihilates Z (Submodule.span Binary {baseEval z})
      (Submodule.span Binary {baseEval z})) :
    Z = Z none none • baseMoment z

end Lax342547.TensorAnnihilators
