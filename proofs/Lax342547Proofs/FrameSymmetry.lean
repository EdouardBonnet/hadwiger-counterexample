import Lax342547.FrameSymmetry
import Lax342547Proofs.PairedFrames
import Lax342547Proofs.FiniteUniform
import Lax342547.PairedFrames
import Lax342547Proofs.LinearExtension

namespace Lax342547Proofs.FrameSymmetry

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry

variable {B H I N : Type} [Fintype B] [Fintype H] [Fintype I] [Fintype N] [DecidableEq N]

theorem injection_change (A A' : Injection I N) : ∃ c : Change N, c.C * A.val = A'.val := by
  classical
  obtain ⟨L, hL⟩ := LinearExtension.extend_injections rfl A.val.mulVecLin A'.val.mulVecLin
    A.property A'.property
  let C := L.toLinearMap.toMatrix'
  let D := L.symm.toLinearMap.toMatrix'
  have hCD : C * D = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  have hDC : D * C = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  refine ⟨⟨C, D, hCD, hDC⟩, ?_⟩
  have he : L.toLinearMap.comp A.val.mulVecLin = A'.val.mulVecLin := LinearMap.ext hL
  simpa only [LinearMap.toMatrix'_comp, PairedFrames.toMatrix_mulVecLin] using
    congrArg LinearMap.toMatrix' he

omit [Fintype I] in
theorem change_mul_injective (c : Change N) :
    Function.Injective (fun A : Matrix N I Binary => c.C * A) := by
  intro A A' h
  have h' := congrArg (fun M => c.D * M) h
  simpa only [← Matrix.mul_assoc, c.DC, Matrix.one_mul] using h'

theorem uniform_of_covariant {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection I N)] (f : Frame B H N E → Injection I N)
    (hf : ∀ c F, (f (transform c F)).val = c.C * (f F).val) :
    (PMF.uniformOfFintype (Frame B H N E)).map f = PMF.uniformOfFintype (Injection I N) := by
  apply FiniteUniform.map_eq_of_transport
  intro A A'
  obtain ⟨c, hc⟩ := injection_change A A'
  refine ⟨frameEquiv c, fun F => ?_⟩
  rw [Subtype.ext_iff, Subtype.ext_iff]
  change (f (transform c F)).val = A'.val ↔ (f F).val = A.val
  rw [hf, ← hc]
  exact (change_mul_injective c).eq_iff

theorem uniform_of_contravariant {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection I N)] (f : Frame B H N E → Injection I N)
    (hf : ∀ c F, (f (transform c F)).val = c.D.transpose * (f F).val) :
    (PMF.uniformOfFintype (Frame B H N E)).map f = PMF.uniformOfFintype (Injection I N) := by
  apply FiniteUniform.map_eq_of_transport
  intro A A'
  obtain ⟨c, hc⟩ := injection_change A A'
  refine ⟨frameEquiv c.dual, fun F => ?_⟩
  rw [Subtype.ext_iff, Subtype.ext_iff]
  change (f (transform c.dual F)).val = A'.val ↔ (f F).val = A.val
  rw [hf]
  simp only [Change.dual, Matrix.transpose_transpose]
  rw [← hc]
  exact (change_mul_injective c).eq_iff

omit [Fintype I] [DecidableEq N] in
/--
---
conclusion: Lax342547.FrameSymmetry.plus_uniform
---
Every two injective plus frames are related by an ambient change. Its
action bijects their raw-frame completions, so all fibers have equal mass.
-/
theorem plus_uniform {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection (B ⊕ H) N)] :
    (PMF.uniformOfFintype (Frame B H N E)).map plus =
      PMF.uniformOfFintype (Injection (B ⊕ H) N) := by
  classical
  apply uniform_of_covariant
  intro c F
  exact (Matrix.mul_fromCols c.C F.P F.X).symm

omit [Fintype I] [DecidableEq N] in
/--
---
conclusion: Lax342547.FrameSymmetry.minus_uniform
---
The inverse-transpose action similarly bijects completions of every
injective combined minus frame.
-/
theorem minus_uniform {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection (B ⊕ H) N)] :
    (PMF.uniformOfFintype (Frame B H N E)).map minus =
      PMF.uniformOfFintype (Injection (B ⊕ H) N) := by
  classical
  apply uniform_of_contravariant
  intro c F
  exact (Matrix.mul_fromCols c.D.transpose F.Q F.Y).symm

omit [Fintype I] [DecidableEq N] in
/--
---
conclusion: Lax342547.FrameSymmetry.plusChannel_uniform
---
Transitivity and equal completion counts also hold for the plus channel
alone, giving its unconditional uniform injective-frame law.
-/
theorem plusChannel_uniform {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection H N)] :
    (PMF.uniformOfFintype (Frame B H N E)).map plusChannel =
      PMF.uniformOfFintype (Injection H N) := by
  classical
  apply uniform_of_covariant
  intro c F
  rfl

omit [Fintype I] [DecidableEq N] in
/--
---
conclusion: Lax342547.FrameSymmetry.minusChannel_uniform
---
The dual ambient action gives the uniform injective-frame law for the
minus channel alone.
-/
theorem minusChannel_uniform {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    [Nonempty (Injection H N)] :
    (PMF.uniformOfFintype (Frame B H N E)).map minusChannel =
      PMF.uniformOfFintype (Injection H N) := by
  classical
  apply uniform_of_contravariant
  intro c F
  rfl

omit [Fintype I] in
/--
---
conclusion: Lax342547.FrameSymmetry.full_frame_orbit
---
Fixing the channel Gram fixes the entire block Gram of the combined
frames. The paired-matrix orbit theorem therefore transports every raw
frame to every other frame with that same channel Gram.
-/
theorem full_frame_orbit {E : Matrix B B Binary} (F G : Frame B H N E)
    (hchannel : F.X.transpose * F.Y = G.X.transpose * G.Y) :
    ∃ c : Change N, transform c F = G := by
  have hgram : (plus F).val.transpose * (minus F).val =
      (plus G).val.transpose * (minus G).val := by
    simp only [plus, minus, Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
      F.gram, G.gram, F.plus_annihilator, G.plus_annihilator,
      F.minus_annihilator, G.minus_annihilator, hchannel]
  obtain ⟨C, D, hCD, hDC, hplus, hminus⟩ := Lax342547.PairedFrames.paired_matrix_orbit
    (plus F).val (plus G).val (minus F).val (minus G).val
    (plus F).property (plus G).property (minus F).property (minus G).property hgram
  change C * Matrix.fromCols F.P F.X = Matrix.fromCols G.P G.X at hplus
  change D.transpose * Matrix.fromCols F.Q F.Y = Matrix.fromCols G.Q G.Y at hminus
  rw [Matrix.mul_fromCols] at hplus hminus
  have hplus := Matrix.fromCols_inj hplus
  have hminus := Matrix.fromCols_inj hminus
  refine ⟨⟨C, D, hCD, hDC⟩, frameData_injective ?_⟩
  exact Prod.ext hplus.1 (Prod.ext hminus.1 (Prod.ext hplus.2 hminus.2))

end Lax342547Proofs.FrameSymmetry
