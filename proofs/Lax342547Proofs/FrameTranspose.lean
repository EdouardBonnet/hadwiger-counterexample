import Lax342547.FrameTranspose
import Lax342547.ChannelColumns
import Lax342547.PhaseAverages
import Lax342547.UnitSpanAvoidance

namespace Lax342547Proofs.FrameTranspose
open Lax342547.FrameTranspose

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.RealCellLaws
open Lax342547.PushforwardWalsh Lax342547.RetainedImages
open scoped BigOperators

/--
---
conclusion: Lax342547.FrameTranspose.uniform_equiv_push
---
-/
theorem uniform_equiv_push {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (b : B) :
    push (weights (PMF.uniformOfFintype A)) e b = weights (PMF.uniformOfFintype B) b := by
  classical
  unfold push
  have he : (∑ a : A,if e a = b then weights (PMF.uniformOfFintype A) a else 0) =
      weights (PMF.uniformOfFintype A) (e.symm b) := by
    rw [Finset.sum_eq_single (e.symm b)]
    · simp
    · intro a _ ha
      exact if_neg (fun h => ha (e.injective (h.trans (e.apply_symm_apply b).symm)))
    · simp
  rw [he]
  simp only [weights,PMF.uniformOfFintype_apply,Fintype.card_congr e]

/--
---
conclusion: Lax342547.FrameTranspose.capped_transpose_frame
---
-/
theorem capped_transpose_frame {A P H N : Type} [Fintype A] [Fintype P] [Fintype H] [Fintype N]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (image : A → Frame P H N E) (M : ℝ)
    (hcap : ∀ f,push α image f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f) :
    letI : Nonempty (Frame P H N E.transpose) := ⟨transposeFrame (Classical.choice inferInstance)⟩
    ∀ f,push α (fun a => transposeFrame (image a)) f ≤
      M*weights (PMF.uniformOfFintype (Frame P H N E.transpose)) f := by
  letI : Nonempty (Frame P H N E.transpose) := ⟨transposeFrame (Classical.choice inferInstance)⟩
  intro f
  have he := Lax342547.ChannelColumns.push_cell_mass α image (fun g => transposeFrame g = f)
  have hh := Lax342547.PhaseAverages.finite_event_density
    (weights (PMF.uniformOfFintype (Frame P H N E))) (push α image) M hcap (fun g => transposeFrame g = f)
  change cellMass α (fun a => transposeFrame (image a) = f) ≤ _
  rw [← he]
  have hu := Lax342547.FrameTranspose.uniform_equiv_push (transposeEquiv (H := H) (N := N) E) f
  change cellMass (weights (PMF.uniformOfFintype (Frame P H N E))) (fun g => transposeFrame g = f) = _ at hu
  exact hh.trans_eq (congrArg (fun x => M*x) hu)

/--
---
conclusion: Lax342547.FrameTranspose.conditioned_dual_span_avoidance
---
-/
theorem conditioned_dual_span_avoidance {A P H N : Type}
    [Fintype A] [Fintype P] [Fintype H] [Fintype N] [DecidableEq P] [DecidableEq H] [DecidableEq N]
    (E : Matrix P P Binary) [Nonempty (Frame P H N E)]
    (α : A → ℝ) (image : A → Frame P H N E) (V : A → Submodule Binary (N → Binary))
    (W : Submodule Binary (N → Binary)) (C : A → Prop) (M τ : ℝ)
    (hα : ∀ a,0 ≤ α a) (hM : 0 ≤ M) (hτ : 0 < τ) (hC : τ ≤ cellMass α C)
    (hN : Fintype.card P+Fintype.card H+1 ≤ Fintype.card N)
    (hV : ∀ a,V a ≤ LinearMap.range (image a).Q.mulVecLin)
    (hcap : ∀ f,push α image f ≤ M*weights (PMF.uniformOfFintype (Frame P H N E)) f) :
    cellMass (Lax342547.RetainedImages.conditionalLaw α C) (fun a => ¬ Disjoint (V a) W) ≤
      (M/τ)*(2*((2 : ℝ)^(Fintype.card P+Fintype.card H+Module.finrank Binary W)/(2 : ℝ)^Fintype.card N)) := by
  letI : Nonempty (Frame P H N E.transpose) := ⟨transposeFrame (Classical.choice inferInstance)⟩
  exact Lax342547.UnitSpanAvoidance.conditioned_unit_span_avoidance E.transpose α
    (fun a => transposeFrame (image a)) V W C M τ hα hM hτ hC hN hV
    (Lax342547.FrameTranspose.capped_transpose_frame E α image M hcap)

end Lax342547Proofs.FrameTranspose
