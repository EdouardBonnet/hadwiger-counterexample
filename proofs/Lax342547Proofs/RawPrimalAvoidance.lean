import Lax342547.RawPrimalAvoidance
import Lax342547Proofs.InjectiveDensity
import Lax342547Proofs.PrimalAvoidance
import Lax342547Proofs.InjectiveFrames
import Lax342547Proofs.ChannelColumns
import Lax342547Proofs.PhaseAverages

namespace Lax342547Proofs.RawPrimalAvoidance
open Lax342547.RawPrimalAvoidance

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry
open Lax342547.RealCellLaws Lax342547.RetainedImages Lax342547.PushforwardWalsh
open scoped BigOperators

/--
---
conclusion: Lax342547.RawPrimalAvoidance.plus_matrix_point_cap
---
-/
theorem plus_matrix_point_cap {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq B] [DecidableEq H] [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] (hN : Fintype.card B+Fintype.card H+1 ≤ Fintype.card N)
    (Z : Matrix N (B ⊕ H) Binary) :
    push (weights (PMF.uniformOfFintype (Frame B H N E))) (fun F => (plus F).val) Z ≤
      2*weights (PMF.uniformOfFintype (Matrix N (B ⊕ H) Binary)) Z := by
  haveI : Nonempty (Injection (B ⊕ H) N) := Nonempty.map (plus (E := E)) (inferInstance : Nonempty (Frame B H N E))
  have ht := congrArg (PMF.map (Subtype.val : Injection (B ⊕ H) N → Matrix N (B ⊕ H) Binary))
    (Lax342547Proofs.FrameSymmetry.plus_uniform (E := E))
  rw [PMF.map_comp] at ht
  have he : (PMF.uniformOfFintype (Frame B H N E)).map (fun F => (plus F).val) =
      (PMF.uniformOfFintype (Injection (B ⊕ H) N)).map Subtype.val := ht
  rw [← Lax342547Proofs.ChannelColumns.pmf_weights_map,he,
    Lax342547Proofs.ChannelColumns.pmf_weights_map]
  exact Lax342547Proofs.InjectiveDensity.injective_matrix_point_cap (by simpa only [Fintype.card_sum] using hN) Z

/--
---
conclusion: Lax342547.RawPrimalAvoidance.raw_primal_span_hit_mass
---
-/
theorem raw_primal_span_hit_mass {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq B] [DecidableEq H] [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] (hN : Fintype.card B+Fintype.card H+1 ≤ Fintype.card N)
    (W : Submodule Binary (N → Binary)) :
    cellMass (weights (PMF.uniformOfFintype (Frame B H N E)))
      (fun F => ∃ c : B → Binary,c ≠ 0 ∧ F.P.mulVec c ∈ W) ≤
      2*((2 : ℝ)^(Fintype.card B+Fintype.card H+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N) := by
  classical
  let ρ := weights (PMF.uniformOfFintype (Frame B H N E))
  let f := fun F : Frame B H N E => (plus F).val
  have hm : cellMass ρ (fun F => ∃ c : B → Binary,c ≠ 0 ∧ F.P.mulVec c ∈ W) ≤
      cellMass ρ (fun F => ∃ c : (B ⊕ H) → Binary,c ≠ 0 ∧ (f F).mulVec c ∈ W) := by
    apply Lax342547Proofs.FiniteSampling.cell_mass_mono _ _ _ (Lax342547Proofs.RealCellLaws.weights_nonneg _)
    rintro F ⟨c,hc,hW⟩
    refine ⟨Sum.elim c 0,?_,?_⟩
    · intro hz
      apply hc
      funext b
      exact congrFun hz (.inl b)
    · simpa only [f,plus,Matrix.fromCols_mulVec,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
        Matrix.mulVec_zero,add_zero] using hW
  have hp := Lax342547Proofs.ChannelColumns.push_cell_mass ρ f
    (fun A : Matrix N (B ⊕ H) Binary => ∃ c : (B ⊕ H) → Binary,c ≠ 0 ∧ A.mulVec c ∈ W)
  have hm' := hm.trans_eq hp.symm
  have hh := Lax342547Proofs.PrimalAvoidance.capped_matrix_span_hit (push ρ f) 2 (by norm_num)
    (fun Z => plus_matrix_point_cap E hN Z) W
  exact hm'.trans (by simpa only [Fintype.card_sum] using hh)

end Lax342547Proofs.RawPrimalAvoidance
