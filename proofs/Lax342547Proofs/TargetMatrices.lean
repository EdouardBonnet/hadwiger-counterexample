import Lax342547.TargetMatrices
import Lax342547.Atoms
import Lax342547.BaseCompression
import Lax342547.StarRouting
import Lax342547.TargetTesters
import Lax342547Proofs.ConcreteCut
import Lax342547Proofs.UnaryMixer

namespace Lax342547Proofs.TargetMatrices
open Lax342547.TargetMatrices

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.Atoms
open Lax342547.PairedWitnesses Lax342547.WitnessAtoms Lax342547.TargetTesters

/--
---
conclusion: Lax342547.TargetMatrices.sandwich_adjoint
---
-/
theorem sandwich_adjoint {B : Type} [Fintype B] (M W L R : Matrix B B Binary) :
    matrixPair M (L * W * R.transpose) = matrixPair (L.transpose * M * R) W := by
  classical
  simp only [Lax342547.BaseCompression.matrixPair_trace, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

/--
---
conclusion: Lax342547.TargetMatrices.mixer_matrix_representation
---
-/
theorem mixer_matrix_representation {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (v x : Profile k n b degree) :
    (∑ e, matrixPair (mixerMatrix L R v e) (x.val e)) = mixingForm L R v x + mixingForm L R x v := by
  classical
  change (∑ e, matrixPairing (mixerMatrix L R v e) (x.val e)) = _
  simp only [mixerMatrix, map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply]
  rw [Finset.sum_add_distrib, Lax342547Proofs.ConcreteCut.mixingForm_apply,
    Lax342547Proofs.ConcreteCut.mixingForm_apply]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    apply Finset.sum_congr rfl
    intro e _
    exact (Lax342547.TargetMatrices.sandwich_adjoint _ _ _ _).symm
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    exact Lax342547Proofs.UnaryMixer.matrixPair_comm _ _

/--
---
conclusion: Lax342547.TargetMatrices.witness_component_rank
---
-/
theorem witness_component_rank {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr) (i z : Fin 2) (e : Component (Tag k)) :
    ((leftWitness W i z).val e).rank ≤ 7 := by
  classical
  have he : (leftWitness W i z).val e = ∑ j, (W.left i z j).profile.val e := by
    simp only [leftWitness, Submodule.coe_sum, Finset.sum_apply]
  rw [he]
  have h := Lax342547.StarRouting.matrix_sum_rank (fun j : Fin (W.length i z) =>
    (W.left i z j).profile.val e)
  have hj (j : Fin (W.length i z)) : ((W.left i z j).profile.val e).rank ≤ 1 := by
    rw [PointAtom.profile, Lax342547.Atoms.atom_component]
    split_ifs
    · exact Matrix.rank_vecMulVec_le _ _
    · simp
  have hs : (∑ j : Fin (W.length i z), ((W.left i z j).profile.val e).rank) ≤ W.length i z := by
    have h' := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hj j)
    simpa using h'
  exact (h.trans hs).trans (W.short i z)

/--
---
conclusion: Lax342547.TargetMatrices.mixer_matrix_rank
---
-/
theorem mixer_matrix_rank {k n b degree J : ℕ}
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (v : Profile k n b degree) (S : ℕ) (hS : ∀ f, (v.val f).rank ≤ S)
    (e : Component (Tag k)) : (mixerMatrix L R v e).rank ≤
      2 * J * Fintype.card (Component (Tag k)) * S := by
  classical
  have hf (j : Fin J) (f : Component (Tag k)) :
      ((L j f e).transpose * v.val f * R j f e).rank ≤ S :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans (hS f)
  have hr (j : Fin J) (f : Component (Tag k)) :
      (L j e f * v.val f * (R j e f).transpose).rank ≤ S :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans (hS f)
  have hs (M : Fin J → Component (Tag k) → Moment k n b degree)
      (hM : ∀ j f, (M j f).rank ≤ S) :
      (∑ j, ∑ f, M j f).rank ≤ J * Fintype.card (Component (Tag k)) * S := by
    have h := Lax342547.StarRouting.matrix_sum_rank (fun j => ∑ f, M j f)
    have h' : (∑ j : Fin J, (∑ f, M j f).rank) ≤
        ∑ _ : Fin J, Fintype.card (Component (Tag k)) * S := by
      apply Finset.sum_le_sum
      intro j _
      exact Lax342547.StarRouting.matrix_finset_sum_rank Finset.univ (M j) S (fun f _ => hM j f)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      Nat.mul_assoc] using h.trans h'
  have h := Lax342547.StarRouting.matrix_add_rank
    (∑ j, ∑ f, (L j f e).transpose * v.val f * R j f e)
    (∑ j, ∑ f, L j e f * v.val f * (R j e f).transpose)
  have h₁ := hs _ hf
  have h₂ := hs _ hr
  change (mixerMatrix L R v e).rank ≤ _ at h
  exact h.trans (by nlinarith)



/--
---
conclusion: Lax342547.TargetMatrices.target_matrix_rank
---
-/
theorem target_matrix_rank {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (i z : Fin 2) (e : Component (Tag k)) :
    (targetMatrix W D L R i z e).rank ≤ 15 * r + 14 * J * Fintype.card (Component (Tag k)) := by
  have ht := Lax342547.TargetTesters.witness_tester_rank W D i z e
  have hm := Lax342547.TargetMatrices.mixer_matrix_rank L R (leftWitness W i z) 7 (Lax342547.TargetMatrices.witness_component_rank W i z) e
  have ha := Lax342547.StarRouting.matrix_add_rank
    (witnessTesterMatrix W D i z e) (mixerMatrix L R (leftWitness W i z) e)
  exact ha.trans (by nlinarith)

/--
---
conclusion: Lax342547.TargetMatrices.target_matrix_representation
---
-/
theorem target_matrix_representation {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (i z : Fin 2) (hodd : (∑ j, diagonalBit hr (W.left i z j)) = 1)
    (x : Profile k n b degree) :
    (∑ e, matrixPair (targetMatrix W D L R i z e) (x.val e)) =
      (D.role + gradient D L R (leftWitness W i z)) x := by
  classical
  change (∑ e, matrixPairing (targetMatrix W D L R i z e) (x.val e)) = _
  simp only [targetMatrix, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  have ht := Lax342547.TargetTesters.witness_tester_representation W D i z hodd x
  change (∑ e, matrixPairing (witnessTesterMatrix W D i z e) (x.val e)) = _ at ht
  have hm := Lax342547.TargetMatrices.mixer_matrix_representation L R (leftWitness W i z) x
  change (∑ e, matrixPairing (mixerMatrix L R (leftWitness W i z) e) (x.val e)) = _ at hm
  rw [ht, hm]
  simp only [testerTarget, gradient, Lax342547.GradientForm.form, LinearMap.add_apply,
    LinearMap.BilinForm.flip, LinearMap.BilinForm.flipHom, map_zero, add_zero]
  abel

/--
---
conclusion: Lax342547.TargetMatrices.target_family_representation
---
-/
theorem target_family_representation {k n b degree r J : ℕ} {hr : 2 * r ≤ n}
    (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr)
    (L R : Fin J → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (z : Fin 2) (hodd : ∀ i, (∑ j, diagonalBit hr (W.left i z j)) = 1) :
    Lax342547.ResidualRealization.matrixResponse (Profile k n b degree) (fun i => targetMatrix W D L R i z) =
      ∑ i, (D.role + gradient D L R (leftWitness W i z)).comp (LinearMap.proj i) := by
  classical
  apply LinearMap.ext
  intro x
  simp only [Lax342547.ResidualRealization.matrixResponse, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact Lax342547.TargetMatrices.target_matrix_representation W D L R i z (hodd i) (x i)

end Lax342547Proofs.TargetMatrices
