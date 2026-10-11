import Lax342547.LabelRelations
import Lax342547Proofs.CutProfiles
import Lax342547.SelectorInterpolation

namespace Lax342547Proofs.LabelRelations

open Lax342547.MomentSpace Lax342547.ConcreteGeometry Lax342547.TensorBlocks
open Lax342547.CutProfiles Lax342547.LabelRelations

set_option backward.isDefEq.respectTransparency false

/--
---
conclusion: Lax342547.LabelRelations.blocks_unique
---
Read the column whose selector is the empty monomial. For each base
entry the resulting relation is a linear relation among distinct
selector evaluations, and interpolation recovers every coefficient.
-/
theorem blocks_unique {Base : Type} [Fintype Base] {b degree : ℕ}
    (L : Finset (Fin b → Binary)) (Z : (Fin b → Binary) → Matrix Base Base Binary)
    (hdegree : L.card ≤ degree + 1) (h : (∑ s ∈ L, block (selectorEval (degree := degree)) s (Z s)) = 0) :
    ∀ s ∈ L, Z s = 0 := by
  classical
  have hli := Lax342547.SelectorInterpolation.selectorEval_linearIndependent
    (fun s : L => s.val) Subtype.val_injective (by simpa using hdegree)
  rw [← Finset.sum_coe_sort L] at h
  intro s hs
  ext i j
  have he : (∑ t : L, Z t.val i j • selectorEval (degree := degree) t.val) = 0 := by
    ext c
    have hc := congrArg (fun M => M (c, i) (emptySelector b degree, j)) h
    simpa [Matrix.sum_apply, block, selectorEval, emptySelector,
      Pi.smul_apply, smul_eq_mul, mul_comm, Finset.sum_apply] using hc
  exact (Fintype.linearIndependent_iff.mp hli) (fun t : L => Z t.val i j) he ⟨s, hs⟩

theorem supported_sum {Label Coord Base : Type} [DecidableEq Label]
    (p : Label → Coord → Binary) (L J : Finset Label) (hL : L ⊆ J)
    (Z : Label → Matrix Base Base Binary) :
    (∑ s ∈ J, block p s (supported L Z s)) = ∑ s ∈ L, block p s (Z s) := by
  classical
  have he : (∑ s ∈ L, block p s (supported L Z s)) = ∑ s ∈ L, block p s (Z s) := by
    apply Finset.sum_congr rfl
    intro s hs
    simp [supported, hs]
  rw [← he]
  symm
  apply Finset.sum_subset hL
  intro s _ hs
  simp [supported, hs]

/--
---
conclusion: Lax342547.LabelRelations.triangle_blocks
---
Pad each of the three supports by zero in their union, of size at most
3R. Combine the block sums and apply uniqueness to their labelwise sum.
-/
theorem triangle_blocks {Base : Type} [Fintype Base] {b degree R : ℕ}
    (L : Fin 3 → Finset (Fin b → Binary))
    (Z : Fin 3 → (Fin b → Binary) → Matrix Base Base Binary)
    (hL : ∀ i, (L i).card ≤ R) (hdegree : 3 * R ≤ degree + 1)
    (h : (∑ i, ∑ s ∈ L i, block (selectorEval (degree := degree)) s (Z i s)) = 0) :
    ∀ s, (∑ i, supported (L i) (Z i) s) = 0 := by
  classical
  let J := Finset.univ.biUnion L
  have hsub (i : Fin 3) : L i ⊆ J := by
    intro s hs
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hs⟩
  have hcard : J.card ≤ degree + 1 := by
    calc
      _ ≤ ∑ i : Fin 3, (L i).card := Finset.card_biUnion_le
      _ ≤ ∑ i : Fin 3, R := Finset.sum_le_sum (fun i _ => hL i)
      _ = 3 * R := by simp [Nat.mul_comm]
      _ ≤ degree + 1 := hdegree
  have hz : (∑ s ∈ J, block (selectorEval (degree := degree)) s
      (∑ i, supported (L i) (Z i) s)) = 0 := by
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    simp_rw [supported_sum _ _ _ (hsub _)]
    exact h
  intro s
  by_cases hs : s ∈ J
  · exact Lax342547.LabelRelations.blocks_unique J _ hcard hz s hs
  · have hout (i : Fin 3) : s ∉ L i := fun hsi => hs (hsub i hsi)
    simp [supported, hout]

theorem binary_double {V : Type} [AddCommGroup V] [Module Binary V] (v : V) : v + v = 0 := by
  have h2 : (1 + 1 : Binary) = 0 := rfl
  calc
    v + v = (1 + 1 : Binary) • v := by rw [add_smul]; simp
    _ = 0 := by rw [h2, zero_smul]

/--
---
conclusion: Lax342547.LabelRelations.cut_triangle
---
Each representative value occurs twice among the three cut edges,
so the triangle sum vanishes in characteristic two.
-/
theorem cut_triangle {Tag V : Type} [DecidableEq Tag] [AddCommGroup V] [Module Binary V]
    (w : Tag → V) (a b c : Tag) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cutMap w (edge a b hab) + cutMap w (edge b c hbc) + cutMap w (edge a c hac) = 0 := by
  rw [edge, edge, edge, CutProfiles.cutMap_pair w hab,
    CutProfiles.cutMap_pair w hbc, CutProfiles.cutMap_pair w hac]
  calc
    (w a + w b) + (w b + w c) + (w a + w c) =
        (w a + w a) + (w b + w b) + (w c + w c) := by abel
    _ = 0 := by simp [binary_double]

end Lax342547Proofs.LabelRelations
