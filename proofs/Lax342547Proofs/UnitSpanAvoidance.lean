import Lax342547.UnitSpanAvoidance
import Lax342547.ChannelColumns
import Lax342547.FiniteSampling
import Lax342547.PhaseAverages
import Lax342547.RawPrimalAvoidance
import Lax342547.RealCellLaws
import Lax342547.RetainedImages

namespace Lax342547Proofs.UnitSpanAvoidance
open Lax342547.UnitSpanAvoidance

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RelativeEntropy Lax342547.RetainedImages
open Lax342547.RawFrames Lax342547.FrameSymmetry Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped BigOperators

/--
---
conclusion: Lax342547.UnitSpanAvoidance.pin_intersection_is_primal_hit
---
-/
theorem pin_intersection_is_primal_hit {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    {E : Matrix B B Binary} (F : Frame B H N E) (V W : Submodule Binary (N → Binary))
    (hV : V ≤ LinearMap.range F.P.mulVecLin) (hbad : ¬ Disjoint V W) :
    ∃ c : B → Binary,c ≠ 0 ∧ F.P.mulVec c ∈ W := by
  have hn : V ⊓ W ≠ ⊥ := fun h => hbad (disjoint_iff.mpr h)
  obtain ⟨v,hv,hv0⟩ := (V ⊓ W).ne_bot_iff.mp hn
  obtain ⟨c,hc⟩ := hV hv.1
  refine ⟨c,?_,?_⟩
  · intro hz
    apply hv0
    rw [hz,map_zero] at hc
    exact hc.symm
  · have hc' : F.P.mulVec c = v := hc
    rw [hc']
    exact hv.2

/--
---
conclusion: Lax342547.UnitSpanAvoidance.capped_unit_span_avoidance
---
-/
theorem capped_unit_span_avoidance {A B H N : Type}
    [Fintype A] [Fintype B] [Fintype H] [Fintype N] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (α : A → ℝ) (image : A → Frame B H N E) (V : A → Submodule Binary (N → Binary))
    (W : Submodule Binary (N → Binary)) (M : ℝ) (hα : ∀ a,0 ≤ α a) (hM : 0 ≤ M)
    (hN : Fintype.card B+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (image a).P.mulVecLin)
    (hcap : ∀ F,push α image F ≤ M*weights (PMF.uniformOfFintype (Frame B H N E)) F) :
    cellMass α (fun a => ¬ Disjoint (V a) W) ≤
      M*(2*((2 : ℝ)^(Fintype.card B+Fintype.card H+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N)) := by
  let P := fun F : Frame B H N E => ∃ c : B → Binary,c ≠ 0 ∧ F.P.mulVec c ∈ W
  have hm : cellMass α (fun a => ¬ Disjoint (V a) W) ≤ cellMass α (fun a => P (image a)) :=
    Lax342547.FiniteSampling.cell_mass_mono _ _ _ hα
      (fun a ha => Lax342547.UnitSpanAvoidance.pin_intersection_is_primal_hit (image a) (V a) W (hV a) ha)
  have hp := Lax342547.ChannelColumns.push_cell_mass α image P
  have hd := Lax342547.PhaseAverages.finite_event_density
    (weights (PMF.uniformOfFintype (Frame B H N E))) (push α image) M hcap P
  have ht := Lax342547.RawPrimalAvoidance.raw_primal_span_hit_mass E hN W
  exact (hm.trans_eq hp.symm).trans (hd.trans (mul_le_mul_of_nonneg_left ht hM))

/--
---
conclusion: Lax342547.UnitSpanAvoidance.conditioned_unit_span_avoidance
---
-/
theorem conditioned_unit_span_avoidance {A B H N : Type}
    [Fintype A] [Fintype B] [Fintype H] [Fintype N] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (α : A → ℝ) (image : A → Frame B H N E) (V : A → Submodule Binary (N → Binary))
    (W : Submodule Binary (N → Binary)) (C : A → Prop) (M τ : ℝ)
    (hα : ∀ a,0 ≤ α a) (hM : 0 ≤ M) (hτ : 0 < τ) (hC : τ ≤ cellMass α C)
    (hN : Fintype.card B+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (image a).P.mulVecLin)
    (hcap : ∀ F,push α image F ≤ M*weights (PMF.uniformOfFintype (Frame B H N E)) F) :
    cellMass (conditionalLaw α C) (fun a => ¬ Disjoint (V a) W) ≤
      (M/τ)*(2*((2 : ℝ)^(Fintype.card B+Fintype.card H+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N)) := by
  have hcc (F : Frame B H N E) : push (conditionalLaw α C) image F ≤
      (M/τ)*weights (PMF.uniformOfFintype (Frame B H N E)) F := by
    classical
    have he : push (conditionalLaw α C) image F =
        cellMass α (fun a => C a ∧ image a = F) / cellMass α C := by
      unfold push conditionalLaw cellMass
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hc : C a <;> by_cases hf : image a = F <;> simp [hc,hf]
    have hm : cellMass α (fun a => C a ∧ image a = F) ≤ push α image F := by
      change cellMass α (fun a => C a ∧ image a = F) ≤ cellMass α (fun a => image a = F)
      exact Lax342547.FiniteSampling.cell_mass_mono _ _ _ hα (fun _ h => h.2)
    rw [he]
    have ht : 0 < cellMass α C := lt_of_lt_of_le hτ hC
    have hb := (div_le_div_of_nonneg_right (hm.trans (hcap F)) ht.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hM (Lax342547.RealCellLaws.weights_nonneg _ _)) hτ hC)
    simpa only [mul_div_right_comm] using hb
  exact Lax342547.UnitSpanAvoidance.capped_unit_span_avoidance E (conditionalLaw α C) image V W (M/τ)
    (Lax342547.RetainedImages.conditional_law_nonneg α C hα) (div_nonneg hM hτ.le) hN hV hcc

end Lax342547Proofs.UnitSpanAvoidance
