import Lax342547.InjectiveDensity
import Lax342547Proofs.InjectiveFrames
import Lax342547Proofs.ChannelColumns

namespace Lax342547Proofs.InjectiveDensity
open Lax342547.InjectiveDensity

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.FrameSymmetry Lax342547.RawFrames
open Lax342547.RealCellLaws Lax342547.PushforwardWalsh
open scoped ENNReal

/--
---
conclusion: Lax342547.InjectiveDensity.injective_matrix_point_cap
---
-/
theorem injective_matrix_point_cap {H N : Type} [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] [Nonempty (Injection H N)]
    (hN : Fintype.card H+1 ≤ Fintype.card N) (Y : Matrix N H Binary) :
    push (weights (PMF.uniformOfFintype (Injection H N))) Subtype.val Y ≤
      2*weights (PMF.uniformOfFintype (Matrix N H Binary)) Y := by
  have hb := Lax342547Proofs.InjectiveFrames.injection_event_bound hN ({Y} : Set (Matrix N H Binary))
  have he : (PMF.uniformOfFintype (Injection H N)).toOuterMeasure
      {A | A.val ∈ ({Y} : Set (Matrix N H Binary))} =
      ((PMF.uniformOfFintype (Injection H N)).map Subtype.val) Y := by
    rw [← PMF.toOuterMeasure_apply_singleton,PMF.toOuterMeasure_map_apply]
    rfl
  rw [he,PMF.toOuterMeasure_apply_singleton] at hb
  have hf : 2*PMF.uniformOfFintype (Matrix N H Binary) Y ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (PMF.apply_ne_top _ _)
  have hr := ENNReal.toReal_mono hf hb
  rw [← Lax342547Proofs.ChannelColumns.pmf_weights_map]
  simpa only [weights,ENNReal.toReal_mul,ENNReal.toReal_ofNat] using hr

/--
---
conclusion: Lax342547.InjectiveDensity.raw_minus_channel_point_cap
---
-/
theorem raw_minus_channel_point_cap {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] [Nonempty (Injection H N)]
    (hN : Fintype.card H+1 ≤ Fintype.card N) (Y : Matrix N H Binary) :
    push (weights (PMF.uniformOfFintype (Frame B H N E))) (fun F => F.Y) Y ≤
      2*weights (PMF.uniformOfFintype (Matrix N H Binary)) Y := by
  have ht := congrArg (PMF.map (Subtype.val : Injection H N → Matrix N H Binary))
    (Lax342547Proofs.FrameSymmetry.minusChannel_uniform (E := E))
  rw [PMF.map_comp] at ht
  have he : (PMF.uniformOfFintype (Frame B H N E)).map (fun F => F.Y) =
      (PMF.uniformOfFintype (Injection H N)).map Subtype.val := ht
  rw [← Lax342547Proofs.ChannelColumns.pmf_weights_map,he,
    Lax342547Proofs.ChannelColumns.pmf_weights_map]
  exact injective_matrix_point_cap hN Y

/--
---
conclusion: Lax342547.InjectiveDensity.raw_plus_channel_point_cap
---
-/
theorem raw_plus_channel_point_cap {B H N : Type} [Fintype B] [Fintype H] [Fintype N]
    [DecidableEq H] [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] [Nonempty (Injection H N)]
    (hN : Fintype.card H+1 ≤ Fintype.card N) (Y : Matrix N H Binary) :
    push (weights (PMF.uniformOfFintype (Frame B H N E))) (fun F => F.X) Y ≤
      2*weights (PMF.uniformOfFintype (Matrix N H Binary)) Y := by
  have ht := congrArg (PMF.map (Subtype.val : Injection H N → Matrix N H Binary))
    (Lax342547Proofs.FrameSymmetry.plusChannel_uniform (E := E))
  rw [PMF.map_comp] at ht
  have he : (PMF.uniformOfFintype (Frame B H N E)).map (fun F => F.X) =
      (PMF.uniformOfFintype (Injection H N)).map Subtype.val := ht
  rw [← Lax342547Proofs.ChannelColumns.pmf_weights_map,he,
    Lax342547Proofs.ChannelColumns.pmf_weights_map]
  exact injective_matrix_point_cap hN Y

end Lax342547Proofs.InjectiveDensity
