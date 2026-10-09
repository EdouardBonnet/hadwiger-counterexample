import Lax342547.FrameTuples
import Lax342547Proofs.FrameSymmetry

namespace Lax342547Proofs.FrameTuples

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry
open Lax342547.FrameTuples

variable {B H I J N : Type} [Fintype B] [Fintype H] [Fintype I] [Fintype J] [Fintype N]

omit [Fintype B] [Fintype H] in
theorem uniform_of_paired_action {α : Type} [Fintype α] [Nonempty α] [DecidableEq N]
    (G : Matrix I J Binary) [Nonempty (Orbit N G)] (f : α → Orbit N G)
    (act : Change N → α ≃ α)
    (hact : ∀ c x, (f (act c x)).val = (c.C * (f x).val.1, c.D.transpose * (f x).val.2)) :
    (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype (Orbit N G) := by
  apply FiniteUniform.map_eq_of_transport
  intro z z'
  obtain ⟨C, D, hCD, hDC, hplus, hminus⟩ :=
    PairedFrames.paired_matrix_orbit z.val.1 z'.val.1 z.val.2 z'.val.2
      z.property.1 z'.property.1 z.property.2.1 z'.property.2.1
      (z.property.2.2.trans z'.property.2.2.symm)
  let c : Change N := ⟨C, D, hCD, hDC⟩
  refine ⟨act c, fun x => ?_⟩
  rw [Subtype.ext_iff, Subtype.ext_iff, hact]
  change (C * (f x).val.1, D.transpose * (f x).val.2) = z'.val ↔ (f x).val = z.val
  rw [← Prod.eta z'.val, ← Prod.eta z.val, ← hplus, ← hminus,
    Prod.mk.injEq, Prod.mk.injEq]
  exact and_congr (FrameSymmetry.change_mul_injective c).eq_iff
    (FrameSymmetry.change_mul_injective c.dual).eq_iff

/--
---
conclusion: Lax342547.FrameTuples.primal_uniform
---
The primal tuple observation has the prescribed Gram and transforms
covariantly. Transitivity of the paired orbit bijects every pair of
completion fibers, so its pushforward is exactly uniform on the orbit.
-/
theorem primal_uniform [DecidableEq N] {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (C : Matrix B I Binary) (D : Matrix B J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose * E * D))] :
    (PMF.uniformOfFintype (Frame B H N E)).map (primalTuple C D hC hD) =
      PMF.uniformOfFintype (Orbit N (C.transpose * E * D)) := by
  apply uniform_of_paired_action _ _ (fun c => frameEquiv c)
  intro c F
  exact Prod.ext (Matrix.mul_assoc c.C F.P C) (Matrix.mul_assoc c.D.transpose F.Q D)

omit [Fintype I] [Fintype J] in
theorem channelGram_transform [DecidableEq N] (c : Change N) {E : Matrix B B Binary}
    (F : Frame B H N E) :
    (transform c F).X.transpose * (transform c F).Y = F.X.transpose * F.Y := by
  have h : c.C.transpose * c.D.transpose = 1 := by
    simpa using congrArg Matrix.transpose c.DC
  change (c.C * F.X).transpose * (c.D.transpose * F.Y) = _
  simp only [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc c.C.transpose,
    h, Matrix.one_mul]

omit [Fintype I] [Fintype J] in
def channelFiberEquiv [DecidableEq N] (c : Change N)
    {E : Matrix B B Binary} {G : Matrix H H Binary} :
    ChannelFiber (N := N) E G ≃ ChannelFiber (N := N) E G where
  toFun F := ⟨transform c F.val, (channelGram_transform c F.val).trans F.property⟩
  invFun F := ⟨transform c.inv F.val, (channelGram_transform c.inv F.val).trans F.property⟩
  left_inv F := Subtype.ext ((frameEquiv c).left_inv F.val)
  right_inv F := Subtype.ext ((frameEquiv c).right_inv F.val)

/--
---
conclusion: Lax342547.FrameTuples.full_uniform
---
The ambient action preserves the full self-channel Gram. On that fiber,
the combined coefficient tuples therefore have the uniform realization
law with their prescribed block Gram, again by equal completion counts.
-/
theorem full_uniform [DecidableEq N] {E : Matrix B B Binary} {G : Matrix H H Binary}
    [Nonempty (ChannelFiber (N := N) E G)]
    (C : Matrix (B ⊕ H) I Binary) (D : Matrix (B ⊕ H) J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose * fullGram E G * D))] :
    (PMF.uniformOfFintype (ChannelFiber (N := N) E G)).map (fullTuple C D hC hD) =
      PMF.uniformOfFintype (Orbit N (C.transpose * fullGram E G * D)) := by
  apply uniform_of_paired_action _ _ (fun c => channelFiberEquiv c)
  intro c F
  change
    (Matrix.fromCols (c.C * F.val.P) (c.C * F.val.X) * C,
      Matrix.fromCols (c.D.transpose * F.val.Q) (c.D.transpose * F.val.Y) * D) =
    (c.C * (Matrix.fromCols F.val.P F.val.X * C),
      c.D.transpose * (Matrix.fromCols F.val.Q F.val.Y * D))
  rw [← Matrix.mul_fromCols, ← Matrix.mul_fromCols, Matrix.mul_assoc, Matrix.mul_assoc]

/--
---
conclusion: Lax342547.FrameTuples.raw_full_conditioning
---
Filtering and renormalizing the actual raw law at the self-channel Gram
is uniform on that fiber. Its coefficient-tuple image is therefore the
uniform paired-orbit law just proved, with the full block Gram.
-/
theorem raw_full_conditioning [DecidableEq N] {E : Matrix B B Binary} {G : Matrix H H Binary}
    [Nonempty (Frame B H N E)] [Nonempty (ChannelFiber (N := N) E G)]
    (C : Matrix (B ⊕ H) I Binary) (D : Matrix (B ⊕ H) J Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    [Nonempty (Orbit N (C.transpose * fullGram E G * D))]
    (h : ∃ F ∈ {F : Frame B H N E | F.X.transpose * F.Y = G},
      F ∈ (PMF.uniformOfFintype (Frame B H N E)).support) :
    ((PMF.uniformOfFintype (Frame B H N E)).filter {F | F.X.transpose * F.Y = G} h).map
      (fun F => ((plus F).val * C, (minus F).val * D)) =
    (PMF.uniformOfFintype (Orbit N (C.transpose * fullGram E G * D))).map Subtype.val := by
  classical
  let : Nonempty {F : Frame B H N E | F.X.transpose * F.Y = G} := by
    obtain ⟨F, hF, _⟩ := h
    exact ⟨⟨F, hF⟩⟩
  rw [FiniteUniform.filter_uniform (α := Frame B H N E) {F | F.X.transpose * F.Y = G} h]
  rw [← full_uniform C D hC hD, PMF.map_comp, PMF.map_comp]
  rfl

/--
---
conclusion: Lax342547.FrameTuples.primal_product
---
Independent raw draws, indexed by vertices and components together,
give independent primal-tuple orbit laws even when their coefficient
tuples and prescribed Gram matrices vary with the draw.
-/
theorem primal_product {Draw : Type} [Fintype Draw] [DecidableEq Draw] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (C : Draw → Matrix B I Binary) (D : Draw → Matrix B J Binary)
    (hC : ∀ s, Function.Injective (C s).mulVec) (hD : ∀ s, Function.Injective (D s).mulVec)
    [∀ s, Nonempty (Orbit N ((C s).transpose * E * D s))]
    (z : Draw → Matrix N I Binary × Matrix N J Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).map
      (fun o s => ((o s).P * C s, (o s).Q * D s)) z =
    ∏ s, (PMF.uniformOfFintype (Orbit N ((C s).transpose * E * D s))).map Subtype.val (z s) := by
  rw [FiniteUniform.map_fun_apply (fun s (F : Frame B H N E) => (F.P * C s, F.Q * D s))]
  apply Finset.prod_congr rfl
  intro s _
  rw [← primal_uniform (H := H) (C s) (D s) (hC s) (hD s), PMF.map_comp]
  rfl

omit [Fintype I] [Fintype J] in
/--
---
conclusion: Lax342547.FrameTuples.primal_family
---
The product law also allows different tuple dimensions at every vertex
and component. No padding or common-rank restriction is needed.
-/
theorem primal_family {Draw : Type} [Fintype Draw] [DecidableEq Draw] [DecidableEq N]
    {K L : Draw → Type} [∀ s, Fintype (K s)] [∀ s, Fintype (L s)]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (C : ∀ s, Matrix B (K s) Binary) (D : ∀ s, Matrix B (L s) Binary)
    (hC : ∀ s, Function.Injective (C s).mulVec) (hD : ∀ s, Function.Injective (D s).mulVec)
    [∀ s, Nonempty (Orbit N ((C s).transpose * E * D s))]
    (z : ∀ s, Matrix N (K s) Binary × Matrix N (L s) Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).map
      (fun o s => ((o s).P * C s, (o s).Q * D s)) z =
    ∏ s, (PMF.uniformOfFintype (Orbit N ((C s).transpose * E * D s))).map Subtype.val (z s) := by
  rw [FiniteUniform.map_pi_apply (fun s (F : Frame B H N E) => (F.P * C s, F.Q * D s))]
  apply Finset.prod_congr rfl
  intro s _
  rw [← primal_uniform (H := H) (C s) (D s) (hC s) (hD s), PMF.map_comp]
  rfl

omit [Fintype I] [Fintype J] in
/--
---
conclusion: Lax342547.FrameTuples.full_product
---
After specifying each draw's self-channel Gram, the independent
conditional draws retain the product of their full-tuple orbit laws.
Gram values and both tuple dimensions may vary across all draws.
-/
theorem full_product {Draw : Type} [Fintype Draw] [DecidableEq Draw] [DecidableEq N]
    {K L : Draw → Type} [∀ s, Fintype (K s)] [∀ s, Fintype (L s)]
    {E : Matrix B B Binary} (G : Draw → Matrix H H Binary)
    [∀ s, Nonempty (ChannelFiber (N := N) E (G s))]
    (C : ∀ s, Matrix (B ⊕ H) (K s) Binary) (D : ∀ s, Matrix (B ⊕ H) (L s) Binary)
    (hC : ∀ s, Function.Injective (C s).mulVec) (hD : ∀ s, Function.Injective (D s).mulVec)
    [∀ s, Nonempty (Orbit N ((C s).transpose * fullGram E (G s) * D s))]
    (z : ∀ s, Matrix N (K s) Binary × Matrix N (L s) Binary) :
    (PMF.uniformOfFintype (∀ s, ChannelFiber (N := N) E (G s))).map
      (fun o s => ((plus (o s).val).val * C s, (minus (o s).val).val * D s)) z =
    ∏ s, (PMF.uniformOfFintype (Orbit N ((C s).transpose * fullGram E (G s) * D s))).map
      Subtype.val (z s) := by
  rw [FiniteUniform.map_pi_apply (fun s (F : ChannelFiber (N := N) E (G s)) =>
    ((plus F.val).val * C s, (minus F.val).val * D s))]
  apply Finset.prod_congr rfl
  intro s _
  rw [← full_uniform (C s) (D s) (hC s) (hD s), PMF.map_comp]
  rfl

end Lax342547Proofs.FrameTuples
