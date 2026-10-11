import Lax342547.PrimalAvoidance
import Lax342547Proofs.FiniteLinearLaw
import Lax342547Proofs.ChannelColumns
import Lax342547Proofs.InjectiveFrames
import Lax342547Proofs.PhaseAverages

namespace Lax342547Proofs.PrimalAvoidance
open Lax342547.PrimalAvoidance

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RetainedImages Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped BigOperators ENNReal

/--
---
conclusion: Lax342547.PrimalAvoidance.evalMatrix_surjective
---
-/
theorem evalMatrix_surjective {B N : Type} [Fintype B] [DecidableEq B]
    (c : B → Binary) (hc : c ≠ 0) : Function.Surjective (evalMatrix (N := N) c) := by
  classical
  have hex : ∃ j,c j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hc (funext hn)
  obtain ⟨j,hj⟩ := hex
  have hj1 : c j = 1 := (Lax342547Proofs.Walsh.binary_cases (c j)).resolve_left hj
  intro v
  refine ⟨fun i k => if k = j then v i else 0,?_⟩
  funext i
  simp [evalMatrix,Matrix.mulVec,dotProduct,hj1]

/--
---
conclusion: Lax342547.PrimalAvoidance.matrix_vector_uniform
---
-/
theorem matrix_vector_uniform {B N : Type} [Fintype B] [Fintype N]
    [DecidableEq B] [DecidableEq N] (c : B → Binary) (hc : c ≠ 0) :
    (PMF.uniformOfFintype (Matrix N B Binary)).map (fun A : Matrix N B Binary => A.mulVec c) =
      PMF.uniformOfFintype (N → Binary) := by
  exact Lax342547Proofs.FiniteLinearLaw.uniform_image_of_surjective (evalMatrix c) (evalMatrix_surjective c hc)

/--
---
conclusion: Lax342547.PrimalAvoidance.uniform_subspace_mass
---
-/
theorem uniform_subspace_mass {N : Type} [Fintype N] [DecidableEq N] (W : Submodule Binary (N → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (N → Binary))) (fun v => v ∈ W) =
      (2 : ℝ)^Module.finrank Binary W/(2 : ℝ)^Fintype.card N := by
  classical
  rw [Lax342547Proofs.RealCellLaws.event_mass,PMF.toOuterMeasure_uniformOfFintype_apply]
  change ((Fintype.card W : ℝ≥0∞)/(Fintype.card (N → Binary) : ℝ≥0∞)).toReal = _
  rw [Lax342547Proofs.FiniteLinearLaw.binary_card W]
  have hn : Fintype.card (N → Binary) = 2^Fintype.card N := by simp [ZMod.card]
  rw [hn,ENNReal.toReal_div]
  simp only [Nat.cast_pow,Nat.cast_ofNat,ENNReal.toReal_pow,ENNReal.toReal_ofNat]

/--
---
conclusion: Lax342547.PrimalAvoidance.fixed_vector_subspace_mass
---
-/
theorem fixed_vector_subspace_mass {B N : Type} [Fintype B] [Fintype N]
    [DecidableEq B] [DecidableEq N] (c : B → Binary) (hc : c ≠ 0) (W : Submodule Binary (N → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N B Binary))) (fun A => A.mulVec c ∈ W) =
      (2 : ℝ)^Module.finrank Binary W/(2 : ℝ)^Fintype.card N := by
  have ht := matrix_vector_uniform (N := N) c hc
  have he : push (weights (PMF.uniformOfFintype (Matrix N B Binary))) (fun A : Matrix N B Binary => A.mulVec c) =
      weights (PMF.uniformOfFintype (N → Binary)) := by
    funext v
    rw [← Lax342547Proofs.ChannelColumns.pmf_weights_map,ht]
  calc
    _ = cellMass (push (weights (PMF.uniformOfFintype (Matrix N B Binary))) (fun A : Matrix N B Binary => A.mulVec c)) (fun v => v ∈ W) :=
      (Lax342547Proofs.ChannelColumns.push_cell_mass _ (fun A : Matrix N B Binary => A.mulVec c) (fun v => v ∈ W)).symm
    _ = _ := by rw [he];exact uniform_subspace_mass W

/--
---
conclusion: Lax342547.PrimalAvoidance.matrix_span_hit_mass
---
-/
theorem matrix_span_hit_mass {B N : Type} [Fintype B] [Fintype N]
    [DecidableEq B] [DecidableEq N] (W : Submodule Binary (N → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (Matrix N B Binary)))
      (fun A => ∃ c : B → Binary,c ≠ 0 ∧ A.mulVec c ∈ W) ≤
      (2 : ℝ)^(Fintype.card B+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N := by
  classical
  let C := {c : B → Binary // c ≠ 0}
  let ρ := weights (PMF.uniformOfFintype (Matrix N B Binary))
  let P := fun c : C => fun A : Matrix N B Binary => A.mulVec c.val ∈ W
  have he : (fun A : Matrix N B Binary => ∃ c : B → Binary,c ≠ 0 ∧ A.mulVec c ∈ W) =
      (fun A => ∃ c : C,P c A) := by
    funext A
    apply propext
    constructor
    · rintro ⟨c,hc,hW⟩;exact ⟨⟨c,hc⟩,hW⟩
    · rintro ⟨c,hW⟩;exact ⟨c.val,c.property,hW⟩
  have hu := Lax342547Proofs.FiniteSampling.cell_mass_union_bound ρ P Finset.univ
    (Lax342547Proofs.RealCellLaws.weights_nonneg _)
  simp only [Finset.mem_univ,true_and] at hu
  have hc : (Fintype.card C : ℝ) ≤ (2 : ℝ)^Fintype.card B := by
    have hh := Fintype.card_le_of_injective (fun c : C => c.val) Subtype.val_injective
    have he : Fintype.card (B → Binary) = 2^Fintype.card B := by simp [ZMod.card]
    rw [he] at hh
    exact_mod_cast hh
  rw [he]
  calc
    _ ≤ ∑ c : C,cellMass ρ (P c) := hu
    _ = ∑ _c : C,(2 : ℝ)^Module.finrank Binary W/(2 : ℝ)^Fintype.card N := by
      apply Finset.sum_congr rfl
      intro c _
      exact fixed_vector_subspace_mass c.val c.property W
    _ = (Fintype.card C : ℝ)*((2 : ℝ)^Module.finrank Binary W/(2 : ℝ)^Fintype.card N) := by simp
    _ ≤ (2 : ℝ)^Fintype.card B*((2 : ℝ)^Module.finrank Binary W/(2 : ℝ)^Fintype.card N) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← mul_div_assoc,← pow_add]

/--
---
conclusion: Lax342547.PrimalAvoidance.capped_matrix_span_hit
---
-/
theorem capped_matrix_span_hit {B N : Type} [Fintype B] [Fintype N]
    [DecidableEq B] [DecidableEq N] (μ : Matrix N B Binary → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hcap : ∀ A,μ A ≤ L*weights (PMF.uniformOfFintype (Matrix N B Binary)) A)
    (W : Submodule Binary (N → Binary)) :
    cellMass μ (fun A => ∃ c : B → Binary,c ≠ 0 ∧ A.mulVec c ∈ W) ≤
      L*((2 : ℝ)^(Fintype.card B+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N) := by
  have hd := Lax342547Proofs.PhaseAverages.finite_event_density
    (weights (PMF.uniformOfFintype (Matrix N B Binary))) μ L hcap
    (fun A => ∃ c : B → Binary,c ≠ 0 ∧ A.mulVec c ∈ W)
  exact hd.trans (mul_le_mul_of_nonneg_left (matrix_span_hit_mass W) hL)

end Lax342547Proofs.PrimalAvoidance
