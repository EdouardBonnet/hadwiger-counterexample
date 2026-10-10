import Lax342547.TensorBlocks
import Lax342547Proofs.TensorAnnihilators
import Lax342547Proofs.UnaryMixer

namespace Lax342547Proofs.TensorBlocks

open Lax342547.MomentSpace Lax342547.SparsePins Lax342547.ConcreteGeometry
open Lax342547.TensorAnnihilators Lax342547.TensorBlocks

set_option backward.isDefEq.respectTransparency false

theorem block_basis {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
    [DecidableEq Base]
    (p : Label → Coord → Binary) (s : Label) (Z : Matrix Base Base Binary) :
    block p s Z = ∑ i, ∑ j, Z i j • Matrix.vecMulVec
      (labelTensor p s (Pi.single i 1)) (labelTensor p s (Pi.single j 1)) := by
  classical
  ext ⟨c, i⟩ ⟨d, j⟩
  simp [block, labelTensor, Matrix.vecMulVec_apply, Pi.single_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/--
---
conclusion: Lax342547.TensorBlocks.block_contraction
---
Expand the base matrix in elementary outer products. Each lifted outer
product contracts to the bilinear form evaluated on its two lifted factors.
-/
theorem block_contraction {Label Coord Base V W : Type} [Fintype Coord] [Fintype Base]
    [AddCommGroup V] [Module Binary V] [AddCommGroup W] [Module Binary W]
    (p : Label → Coord → Binary) (s : Label) (Z : Matrix Base Base Binary)
    (q : (Coord × Base → Binary) →ₗ[Binary] V)
    (r : (Coord × Base → Binary) →ₗ[Binary] W)
    (β : V →ₗ[Binary] W →ₗ[Binary] Binary) : by
  classical
  let : DecidableEq (Coord × Base) := Classical.decEq _
  exact matrixPair (LinearMap.BilinForm.toMatrix' (β.compl₁₂ q r)) (block p s Z) =
      matrixPair (LinearMap.BilinForm.toMatrix'
        (β.compl₁₂ (q.comp (labelTensor p s)) (r.comp (labelTensor p s)))) Z := by
  classical
  let : DecidableEq (Coord × Base) := Classical.decEq _
  rw [block_basis]
  simp only [map_sum, map_smul]
  simp only [UnaryMixer.matrixPair_vecMulVec, Matrix.toBilin'_toMatrix',
    LinearMap.compl₁₂_apply, smul_eq_mul]
  conv_rhs =>
    simp only [matrixPair, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.BilinForm.toMatrix'_apply, LinearMap.compl₁₂_apply,
      LinearMap.comp_apply, smul_eq_mul, matrixEntry, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
---
conclusion: Lax342547.TensorBlocks.quotient_isolation
---
Pull each base quotient form back through the two extractors. All label
blocks except the selected one vanish, so the original annihilation
tests give every base quotient test of the selected block.
-/
theorem quotient_isolation {Label Coord Base : Type} [Fintype Coord] [Fintype Base]
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
    PureAnnihilates (Z s) A B := by
  classical
  let : DecidableEq (Coord × Base) := Classical.decEq _
  intro β
  have ht := h (β.compl₁₂ q r)
  have hb (t : Label) (htL : t ∈ L) :
      pureContraction S T (β.compl₁₂ q r) (block p t (Z t)) =
        if t = s then pureContraction A B β (Z t) else 0 := by
    unfold pureContraction
    have hc := block_contraction p t (Z t) S.mkQ T.mkQ (β.compl₁₂ q r)
    have hc' : matrixPair (LinearMap.BilinForm.toMatrix'
        ((β.compl₁₂ q r).compl₁₂ S.mkQ T.mkQ)) (block p t (Z t)) =
        matrixPair (LinearMap.BilinForm.toMatrix'
          (((β.compl₁₂ q r).compl₁₂ S.mkQ T.mkQ).compl₁₂
            (labelTensor p t) (labelTensor p t))) (Z t) := by
      convert hc using 1
      congr 1
    apply hc'.trans
    by_cases hts : t = s
    · rw [if_pos hts]
      have hform : ((β.compl₁₂ q r).compl₁₂ S.mkQ T.mkQ).compl₁₂
          (labelTensor p t) (labelTensor p t) = β.compl₁₂ A.mkQ B.mkQ := by
        apply LinearMap.ext
        intro u
        apply LinearMap.ext
        intro v
        change β (q (S.mkQ (labelTensor p t u))) (r (T.mkQ (labelTensor p t v))) =
          β (A.mkQ u) (B.mkQ v)
        rw [hq t htL, hr t htL]
        simp [hts]
      rw [hform]
    · rw [if_neg hts]
      have hz : ((β.compl₁₂ q r).compl₁₂ S.mkQ T.mkQ).compl₁₂
          (labelTensor p t) (labelTensor p t) = 0 := by
        apply LinearMap.ext
        intro u
        apply LinearMap.ext
        intro v
        change β (q (S.mkQ (labelTensor p t u))) (r (T.mkQ (labelTensor p t v))) = 0
        rw [hq t htL, hr t htL]
        simp [hts]
      change matrixPair (LinearMap.BilinForm.toMatrix'
        (((β.compl₁₂ q r).compl₁₂ S.mkQ T.mkQ).compl₁₂
          (labelTensor p t) (labelTensor p t))) (Z t) = 0
      rw [hz]
      simp [matrixPair, matrixEntry]
  rw [map_sum] at ht
  have he : (∑ t ∈ L, pureContraction S T (β.compl₁₂ q r) (block p t (Z t))) =
      pureContraction A B β (Z s) := by
    rw [Finset.sum_eq_single s]
    · simpa using hb s hs
    · intro t htL hts
      simpa [hts] using hb t htL
    · exact fun hns => False.elim (hns hs)
  exact he.symm.trans ht

end Lax342547Proofs.TensorBlocks
