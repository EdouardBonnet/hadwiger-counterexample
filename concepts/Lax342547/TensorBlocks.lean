import Lax342547.TensorAnnihilators
import Lax342547.SparsePins

/-!
---
title: Quotient extractors isolate individual tensor label blocks
type: lemma
---
A label block is the tensor lift of a base matrix. Bilinear contraction
commutes with this lift. Extractors that read one label and kill the
others therefore transfer pure annihilation to that base block.
-/

namespace Lax342547.TensorBlocks

open Lax342547.MomentSpace Lax342547.SparsePins Lax342547.ConcreteGeometry
open Lax342547.TensorAnnihilators

def block {Label Coord Base : Type} (p : Label → Coord → Binary) (s : Label) :
    Matrix Base Base Binary →ₗ[Binary] Matrix (Coord × Base) (Coord × Base) Binary where
  toFun Z i j := p s i.1 * p s j.1 * Z i.2 j.2
  map_add' Z W := by ext i j; exact mul_add _ _ _
  map_smul' c Z := by
    ext i j
    change p s i.1 * p s j.1 * (c * Z i.2 j.2) = c * (p s i.1 * p s j.1 * Z i.2 j.2)
    ring

axiom block_contraction {Label Coord Base V W : Type} [Fintype Coord] [Fintype Base]
    [AddCommGroup V] [Module Binary V] [AddCommGroup W] [Module Binary W]
    (p : Label → Coord → Binary) (s : Label) (Z : Matrix Base Base Binary)
    (q : (Coord × Base → Binary) →ₗ[Binary] V)
    (r : (Coord × Base → Binary) →ₗ[Binary] W)
    (β : V →ₗ[Binary] W →ₗ[Binary] Binary) : by
  classical
  letI : DecidableEq (Coord × Base) := Classical.decEq _
  exact matrixPair (LinearMap.BilinForm.toMatrix' (β.compl₁₂ q r)) (block p s Z) =
      matrixPair (LinearMap.BilinForm.toMatrix'
        (β.compl₁₂ (q.comp (labelTensor p s)) (r.comp (labelTensor p s)))) Z

axiom quotient_isolation {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    [DecidableEq Label]
    (p : Label → Coord → Binary) (L : Finset Label) (s : Label) (hs : s ∈ L)
    (Z : Label → Matrix Base Base Binary)
    (S T : Submodule Binary (Coord × Base → Binary))
    (A B : Submodule Binary (Base → Binary))
    (q : ((Coord × Base → Binary) ⧸ S) →ₗ[Binary] ((Base → Binary) ⧸ A))
    (r : ((Coord × Base → Binary) ⧸ T) →ₗ[Binary] ((Base → Binary) ⧸ B))
    (hq : ∀ t ∈ L, ∀ v, q (S.mkQ (labelTensor p t v)) = if t = s then A.mkQ v else 0)
    (hr : ∀ t ∈ L, ∀ v, r (T.mkQ (labelTensor p t v)) = if t = s then B.mkQ v else 0)
    (h : PureAnnihilates (∑ t ∈ L, block p t (Z t)) S T) :
    PureAnnihilates (Z s) A B

end Lax342547.TensorBlocks
