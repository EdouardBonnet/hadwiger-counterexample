import Lax342547.IndependentWitnesses
import Lax342547Proofs.AdaptiveProtection
import Mathlib.LinearAlgebra.DFinsupp

namespace Lax342547Proofs.IndependentWitnesses
open Lax342547.IndependentWitnesses

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws
open scoped BigOperators

/--
---
conclusion: Lax342547.IndependentWitnesses.independent_witness_matrix
---
-/
theorem independent_witness_matrix {I N : Type} [Fintype I]
    (V : I → Submodule Binary (N → Binary)) (hV : iSupIndep V)
    (v : ∀ i,V i) (hv : ∀ i,(v i).val ≠ 0) :
    Function.Injective (Matrix.of (fun n i => (v i).val n)).mulVec := by
  apply Matrix.mulVec_injective_iff.mpr
  exact iSupIndep.linearIndependent V hV (fun i => (v i).property) hv

/--
---
conclusion: Lax342547.IndependentWitnesses.nonzero_witness_card
---
-/
theorem nonzero_witness_card {I N : Type} [Fintype I] [Fintype N]
    (V : I → Submodule Binary (N → Binary)) (K : ℕ) (hK : ∀ i,Module.finrank Binary (V i) ≤ K) :
    Nat.card (∀ i,{v : V i // v.val ≠ 0}) ≤ 2^(K*Fintype.card I) := by
  classical
  let C := ∀ i,{v : V i // v.val ≠ 0}
  let f : C → (∀ i,V i) := fun c i => (c i).val
  have hf : Function.Injective f := by
    intro c d h
    funext i
    exact Subtype.ext (congrFun h i)
  have hc := Fintype.card_le_of_injective f hf
  have hp : Fintype.card (∀ i,V i) ≤ 2^(K*Fintype.card I) := by
    rw [Fintype.card_pi]
    calc
      _ = ∏ i,2^Module.finrank Binary (V i) := by simp only [Lax342547Proofs.FiniteLinearLaw.binary_card]
      _ ≤ ∏ _i : I,2^K := Finset.prod_le_prod' (fun i _ => Nat.pow_le_pow_right (by omega) (hK i))
      _ = _ := by simp [← pow_mul]
  simpa only [Nat.card_eq_fintype_card] using hc.trans hp

/--
---
conclusion: Lax342547.IndependentWitnesses.adaptive_independent_witness_probability
---
-/
theorem adaptive_independent_witness_probability {I H N : Type}
    [Fintype I] [Fintype H] [Fintype N] [DecidableEq I] [DecidableEq H] [DecidableEq N]
    (V : I → Submodule Binary (N → Binary)) (hV : iSupIndep V)
    (S : Matrix N H Binary → Submodule Binary (H → Binary)) (K : ℕ)
    (hK : ∀ i,Module.finrank Binary (V i) ≤ K) (hS : ∀ Y,Module.finrank Binary (S Y) ≤ K) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N H Binary)))
      (fun Y => ∀ i,∃ v : V i,v.val ≠ 0 ∧ Y.transpose.mulVec v.val ∈ S Y) ≤
      (2 : ℝ)^(Fintype.card H*K+2*K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I) := by
  classical
  let C := ∀ i,{v : V i // v.val ≠ 0}
  let D := fun c : C => Matrix.of (fun n i => (c i).val.val n)
  let ρ := weights (PMF.uniformOfFintype (Matrix N H Binary))
  let P := fun c : C => fun Y : Matrix N H Binary => ∀ i,(fun h => (Y.transpose*D c) h i) ∈ S Y
  have hm : cellMass ρ (fun Y => ∀ i,∃ v : V i,v.val ≠ 0 ∧ Y.transpose.mulVec v.val ∈ S Y) ≤
      cellMass ρ (fun Y => ∃ c : C,P c Y) := by
    apply Lax342547Proofs.FiniteSampling.cell_mass_mono _ _ _ (Lax342547Proofs.RealCellLaws.weights_nonneg _)
    intro Y hY
    choose v hv hvS using hY
    refine ⟨fun i => ⟨v i,hv i⟩,?_⟩
    intro i
    exact hvS i
  have hu := Lax342547Proofs.FiniteSampling.cell_mass_union_bound ρ P Finset.univ
    (Lax342547Proofs.RealCellLaws.weights_nonneg _)
  simp only [Finset.mem_univ,true_and] at hu
  have hp (c : C) : cellMass ρ (P c) ≤
      (2 : ℝ)^(Fintype.card H*K+K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I) :=
    Lax342547Proofs.AdaptiveProtection.adaptive_protected_probability (D c)
      (independent_witness_matrix V hV (fun i => (c i).val) (fun i => (c i).property)) S K hS
  have hc : (Fintype.card C : ℝ) ≤ (2 : ℝ)^(K*Fintype.card I) := by
    have hh := nonzero_witness_card V K hK
    rw [Nat.card_eq_fintype_card] at hh
    exact_mod_cast hh
  calc
    _ ≤ ∑ c : C,cellMass ρ (P c) := hm.trans hu
    _ ≤ ∑ _c : C,(2 : ℝ)^(Fintype.card H*K+K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I) :=
      Finset.sum_le_sum (fun c _ => hp c)
    _ = (Fintype.card C : ℝ)*((2 : ℝ)^(Fintype.card H*K+K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)) := by simp
    _ ≤ (2 : ℝ)^(K*Fintype.card I)*((2 : ℝ)^(Fintype.card H*K+K*Fintype.card I)/(2 : ℝ)^(Fintype.card H*Fintype.card I)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← mul_div_assoc,← pow_add]; congr 2; ring

end Lax342547Proofs.IndependentWitnesses
