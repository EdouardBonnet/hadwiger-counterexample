import Lax342547.ChannelDensity
import Lax342547Proofs.FrameSymmetry
import Lax342547Proofs.GramNormalization

namespace Lax342547Proofs.ChannelDensity

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry
open Lax342547.ChannelDensity
open scoped ENNReal

variable {B H N : Type} [Fintype B] [Fintype H] [Fintype N]

/--
---
conclusion: Lax342547.ChannelDensity.same_gram_mass
---
A paired-frame change carrying one channel pair to the other bijects
their full raw-frame completions, giving exactly equal marginal masses.
-/
theorem same_gram_mass [DecidableEq N] (E : Matrix B B Binary)
    [Nonempty (Frame B H N E)] (A A' B B' : Matrix N H Binary)
    (hA : Function.Injective A.mulVec) (hA' : Function.Injective A'.mulVec)
    (hB : Function.Injective B.mulVec) (hB' : Function.Injective B'.mulVec)
    (hG : A.transpose * B = A'.transpose * B') :
    jointLaw E (A, B) = jointLaw E (A', B') := by
  obtain ⟨C, D, hCD, hDC, hplus, hminus⟩ :=
    PairedFrames.paired_matrix_orbit A A' B B' hA hA' hB hB' hG
  let c : Change N := ⟨C, D, hCD, hDC⟩
  apply FiniteUniform.map_apply_eq_of_transport channels (A, B) (A', B') (frameEquiv c)
  intro F
  change (C * F.X, D.transpose * F.Y) = (A', B') ↔ (F.X, F.Y) = (A, B)
  rw [← hplus, ← hminus, Prod.mk.injEq, Prod.mk.injEq]
  exact and_congr (FrameSymmetry.change_mul_injective c).eq_iff
    (FrameSymmetry.change_mul_injective c.dual).eq_iff

theorem zero_of_not_injective (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (z : Matrix N H Binary × Matrix N H Binary)
    (hz : ¬ (Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec)) :
    jointLaw E z = 0 := by
  classical
  rw [jointLaw, PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro F
  have he : z ≠ channels F := by
    intro he
    apply hz
    rw [he]
    exact ⟨(plusChannel F).property, (minusChannel F).property⟩
  simp [he]

/--
---
conclusion: Lax342547.ChannelDensity.point_density
---
The raw mass is constant on each injective Gram orbit and its total
mass is at most one. Independent columns give that orbit mass at least
2^(-h²-2), so the density on every orbit is at most 2^(h²+2).
-/
theorem point_density [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (hN : Fintype.card H + Fintype.card H + 1 ≤ Fintype.card N)
    (z : Matrix N H Binary × Matrix N H Binary) :
    jointLaw E z ≤ (2 : ℝ≥0∞) ^ (Fintype.card H * Fintype.card H + 2) *
      PMF.uniformOfFintype (Matrix N H Binary × Matrix N H Binary) z := by
  classical
  by_cases hz : Function.Injective z.1.mulVec ∧ Function.Injective z.2.mulVec
  · let S : Set (Matrix N H Binary × Matrix N H Binary) :=
      {x | Function.Injective x.1.mulVec ∧ Function.Injective x.2.mulVec ∧
        x.1.transpose * x.2 = z.1.transpose * z.2}
    apply FiniteProbability.point_density_of_constant (jointLaw E) z S
    · intro x hx
      exact same_gram_mass E x.1 z.1 x.2 z.2 hx.1 hz.1 hx.2.1 hz.2 hx.2.2
    · have hg := GramNormalization.normalization_quarter (N := N) (z.1.transpose * z.2) hN
      change 1 / (2 : ℝ≥0∞) ^ (Fintype.card H * Fintype.card H + 2) ≤
        (PMF.uniformOfFintype (Matrix N H Binary × Matrix N H Binary)).toOuterMeasure S at hg
      calc
        (1 : ℝ≥0∞) = 2 ^ (Fintype.card H * Fintype.card H + 2) *
            (1 / 2 ^ (Fintype.card H * Fintype.card H + 2)) := by
          rw [one_div, ENNReal.mul_inv_cancel (by simp) (by simp)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hg zero_le
  · rw [zero_of_not_injective E z hz]
    exact zero_le

/--
---
conclusion: Lax342547.ChannelDensity.event_density
---
Sum the pointwise density bound over any channel event.
-/
theorem event_density [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (hN : Fintype.card H + Fintype.card H + 1 ≤ Fintype.card N)
    (S : Set (Matrix N H Binary × Matrix N H Binary)) :
    (jointLaw E).toOuterMeasure S ≤
      (2 : ℝ≥0∞) ^ (Fintype.card H * Fintype.card H + 2) *
        (PMF.uniformOfFintype (Matrix N H Binary × Matrix N H Binary)).toOuterMeasure S := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, PMF.toOuterMeasure_apply_fintype, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : z ∈ S
  · simpa [hz] using point_density E hN z
  · simp [hz]

/--
---
conclusion: Lax342547.ChannelDensity.all_components_density
---
The reference raw law is a product over components, and so is its channel
pushforward. Multiplying the component bounds gives the paper's fixed
joint density constant 2^(|E|(h²+2)).
-/
theorem all_components_density {Comp : Type} [Fintype Comp] [DecidableEq Comp]
    [DecidableEq H] [DecidableEq N]
    (E : Matrix B B Binary) [Nonempty (Frame B H N E)]
    (hN : Fintype.card H + Fintype.card H + 1 ≤ Fintype.card N)
    (z : Comp → Matrix N H Binary × Matrix N H Binary) :
    (Lax342547.RawLaw.uniformLaw E).map (fun o e => channels (o e)) z ≤
      (2 : ℝ≥0∞) ^ (Fintype.card Comp * (Fintype.card H * Fintype.card H + 2)) *
        PMF.uniformOfFintype (Comp → Matrix N H Binary × Matrix N H Binary) z := by
  rw [Lax342547.RawLaw.uniformLaw, FiniteUniform.map_fun_apply]
  calc
    _ ≤ ∏ e : Comp, ((2 : ℝ≥0∞) ^ (Fintype.card H * Fintype.card H + 2) *
        PMF.uniformOfFintype (Matrix N H Binary × Matrix N H Binary) (z e)) := by
      apply Finset.prod_le_prod'
      intro e _
      exact point_density E hN (z e)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp [PMF.uniformOfFintype_apply, ← pow_mul, Nat.mul_comm, ENNReal.inv_pow]

end Lax342547Proofs.ChannelDensity
