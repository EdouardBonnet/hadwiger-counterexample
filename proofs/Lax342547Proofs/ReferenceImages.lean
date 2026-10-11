import Lax342547.ReferenceImages
import Lax342547.ProductImages
import Lax342547.ProductMinusImages
import Lax342547Proofs.FiniteProbability
import Lax342547Proofs.FiniteUniform
import Lax342547Proofs.FrameSymmetry

namespace Lax342547Proofs.ReferenceImages

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.FrameSymmetry Lax342547.ProductImages
open Lax342547.ReferenceImages
open scoped ENNReal

variable {Draw B H T U N : Type} [Fintype Draw] [Fintype B] [Fintype H]
  [Fintype T] [Fintype U] [Fintype N]

omit [Fintype Draw] [Fintype T] [Fintype U] [Fintype N] in
def primalPart (A : Injection (B ⊕ H) N) : Matrix N B Binary := fun n b => A.val n (Sum.inl b)

omit [Fintype Draw] [Fintype T] [Fintype U] [Fintype N] in
def channelPart (A : Injection (B ⊕ H) N) : Matrix N H Binary := fun n h => A.val n (Sum.inr h)

omit [Fintype Draw] [Fintype T] [Fintype U] [Fintype N] in
theorem parts_eq (A : Injection (B ⊕ H) N) : Matrix.fromCols (primalPart A) (channelPart A) = A.val := by
  ext n j
  cases j <;> rfl

omit [Fintype Draw] [Fintype T] [Fintype U] [Fintype N] in
theorem parts_injective (A : Injection (B ⊕ H) N) :
    Function.Injective (Matrix.fromCols (primalPart A) (channelPart A)).mulVec := by
  rw [parts_eq]
  exact A.property

omit [Fintype Draw] [Fintype T] [Fintype U] in
def plusFiberEquiv {E : Matrix B B Binary} (A : Injection (B ⊕ H) N) :
    {F : Frame B H N E // plus F = A} ≃
      Lax342547.ConditionalMinus.Fiber E (primalPart A) (channelPart A) where
  toFun F := ⟨F.val, congrArg primalPart F.property, congrArg channelPart F.property⟩
  invFun F := ⟨F.val, by
    apply Subtype.ext
    change Matrix.fromCols F.val.P F.val.X = A.val
    simpa only [F.property.1, F.property.2] using parts_eq A⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype T] [Fintype U] in
def familyFiberEquiv {E : Matrix B B Binary} (A : Draw → Injection (B ⊕ H) N) :
    {o : Draw → Frame B H N E // (fun i => plus (o i)) = A} ≃
      (∀ i, Lax342547.ConditionalMinus.Completion E (primalPart (A i)) (channelPart (A i))) :=
  let e : {o : Draw → Frame B H N E // (fun i => plus (o i)) = A} ≃
      (∀ i, {F : Frame B H N E // plus F = A i}) := {
    toFun := fun o i => ⟨o.val i, congrFun o.property i⟩
    invFun := fun o => ⟨fun i => (o i).val, funext (fun i => (o i).property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  e.trans (Equiv.piCongrRight (fun i => (plusFiberEquiv (A i)).trans
    (Lax342547.ConditionalMinus.completionEquiv (parts_injective (A i)))))

omit [Fintype Draw] [Fintype T] [Fintype U] in
theorem plus_surjective [DecidableEq N] {E : Matrix B B Binary} [Nonempty (Frame B H N E)] :
    Function.Surjective (plus : Frame B H N E → Injection (B ⊕ H) N) := by
  intro A
  let F := Classical.choice (inferInstance : Nonempty (Frame B H N E))
  obtain ⟨c, hc⟩ := FrameSymmetry.injection_change (plus F) A
  refine ⟨transform c F, ?_⟩
  apply Subtype.ext
  change Matrix.fromCols (c.C * F.P) (c.C * F.X) = A.val
  rw [← Matrix.mul_fromCols]
  exact hc

/--
---
conclusion: Lax342547.ReferenceImages.joint_cap
---
Disintegrate the actual uniform raw law over its complete plus-frame
observation. Each fiber is the independent product of the checked minus
completion laws. Multiply its uniform joint-minus image bound by the
plus-prescription probability and integrate. The result has factor 4^k
and dimension loss k(d+h), uniformly over both nominal tuple ranks.
-/
theorem joint_cap [DecidableEq Draw] [DecidableEq B] [DecidableEq H]
    [DecidableEq T] [DecidableEq U] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (D : Matrix (Draw × (B ⊕ H)) U Binary)
    (hC : Function.Injective C.mulVec) (hD : Function.Injective D.mulVec)
    (y : Matrix N T Binary) (z : Matrix N U Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).toOuterMeasure
      {o | plusImages C o = y ∧ minusImages D o = z} ≤
      (4 : ℝ≥0∞) ^ Fintype.card Draw /
        2 ^ (Fintype.card N * Fintype.card T + Fintype.card U *
          (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H))) := by
  classical
  let : Nonempty (Injection (B ⊕ H) N) := ⟨plus (Classical.choice (inferInstance : Nonempty (Frame B H N E)))⟩
  let f : (Draw → Frame B H N E) → (Draw → Injection (B ⊕ H) N) := fun o i => plus (o i)
  let : ∀ A, Nonempty {o : Draw → Frame B H N E // f o = A} := fun A => by
    choose o ho using fun i => plus_surjective (E := E) (A i)
    exact ⟨⟨o, funext ho⟩⟩
  let S : Set (Draw → Frame B H N E) := {o | plusImages C o = y ∧ minusImages D o = z}
  let W : Set (Draw → Injection (B ⊕ H) N) := {A | jointMatrix (fun i => (A i).val) * C = y}
  let b : ℝ≥0∞ := 2 ^ Fintype.card Draw / 2 ^ (Fintype.card U *
    (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H)))
  have hm : (PMF.uniformOfFintype (Draw → Frame B H N E)).toOuterMeasure S ≤
      b * ((PMF.uniformOfFintype (Draw → Frame B H N E)).map f).toOuterMeasure W := by
    apply FiniteProbability.uniform_fiber_event_bound f S W b
    · intro o ho
      exact ho.1
    · intro A _
      let P := fun i => primalPart (A i)
      let X := fun i => channelPart (A i)
      let e := familyFiberEquiv (E := E) A
      let : Nonempty (∀ i, Lax342547.ConditionalMinus.Completion E (P i) (X i)) :=
        ⟨e (Classical.choice (inferInstance : Nonempty {o : Draw → Frame B H N E // f o = A}))⟩
      let : ∀ i, Nonempty (Lax342547.ConditionalMinus.Completion E (P i) (X i)) := fun i =>
        ⟨(Classical.choice (inferInstance : Nonempty (∀ i, Lax342547.ConditionalMinus.Completion E (P i) (X i)))) i⟩
      let : ∀ i, Nonempty (Lax342547.ConditionalMinus.ColumnProduct E (P i) (X i)) := fun i =>
        ⟨(Classical.choice (inferInstance : Nonempty (Lax342547.ConditionalMinus.Completion E (P i) (X i)))).val⟩
      have hb := Lax342547.ProductMinusImages.completion_image_bound E P X (fun i => parts_injective (A i)) hN D hD z
      rw [← FiniteUniform.map_equiv e, PMF.map_comp] at hb
      change (PMF.uniformOfFintype {o : Draw → Frame B H N E // f o = A}).map
        (fun o => minusImages D o.val) z ≤ b at hb
      rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply] at hb
      exact le_trans ((PMF.uniformOfFintype {o : Draw → Frame B H N E // f o = A}).toOuterMeasure.mono
        (fun _ ho => ho.2)) hb
  have hp := Lax342547.ProductImages.raw_plus_image_bound (E := E) (by omega) C hC y
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply] at hp
  have hplus : ((PMF.uniformOfFintype (Draw → Frame B H N E)).map f).toOuterMeasure W ≤
      (2 : ℝ≥0∞) ^ Fintype.card Draw / 2 ^ (Fintype.card N * Fintype.card T) := by
    rw [PMF.toOuterMeasure_map_apply]
    exact hp
  calc
    _ ≤ b * ((PMF.uniformOfFintype (Draw → Frame B H N E)).map f).toOuterMeasure W := hm
    _ ≤ b * ((2 : ℝ≥0∞) ^ Fintype.card Draw / 2 ^ (Fintype.card N * Fintype.card T)) :=
      mul_le_mul_of_nonneg_left hplus zero_le
    _ = _ := by
      dsimp [b]
      rw [← ENNReal.mul_div_mul_comm (Or.inl (by simp)) (Or.inl (by simp)), ← mul_pow,
        ← pow_add]
      norm_num
      rw [Nat.add_comm]

/--
---
conclusion: Lax342547.ReferenceImages.joint_rank_cap
---
Extract independent nominal image bases from both tested coefficient
tuples. The original exact-image event implies these basis prescriptions,
so the cap depends on the true nominal ranks even for dependent tuples.
-/
theorem joint_rank_cap [DecidableEq Draw] [DecidableEq B] [DecidableEq H]
    [DecidableEq T] [DecidableEq U] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (C : Matrix (Draw × (B ⊕ H)) T Binary) (D : Matrix (Draw × (B ⊕ H)) U Binary)
    (y : Matrix N T Binary) (z : Matrix N U Binary) :
    (PMF.uniformOfFintype (Draw → Frame B H N E)).toOuterMeasure
      {o | plusImages C o = y ∧ minusImages D o = z} ≤
      (4 : ℝ≥0∞) ^ Fintype.card Draw /
        2 ^ (Fintype.card N * C.rank + D.rank *
          (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H))) := by
  obtain ⟨C', hC'⟩ := Lax342547.ProductImages.rank_restriction C
  obtain ⟨D', hD'⟩ := Lax342547.ProductImages.rank_restriction D
  have hb := Lax342547.ReferenceImages.joint_cap (E := E) hN (C * C') (D * D') hC' hD' (y * C') (z * D')
  simp only [Fintype.card_fin] at hb
  apply le_trans ((PMF.uniformOfFintype (Draw → Frame B H N E)).toOuterMeasure.mono ?_) hb
  intro o ho
  constructor
  · change jointMatrix (fun i => (plus (o i)).val) * (C * C') = _
    rw [← Matrix.mul_assoc]
    exact congrArg (fun M => M * C') ho.1
  · change jointMatrix (fun i => (minus (o i)).val) * (D * D') = _
    rw [← Matrix.mul_assoc]
    exact congrArg (fun M => M * D') ho.2

omit [Fintype T] [Fintype U] in
/--
---
conclusion: Lax342547.ReferenceImages.all_components_cap
---
Reindex the independent raw draws by component and multiply their exact
image bounds. Both tuple dimensions and ranks may vary arbitrarily with
the component. This gives the finite reference cap with every rank and
conditioning cost explicit, before the final parameter payment.
-/
theorem all_components_cap {Comp : Type} [Fintype Comp] [DecidableEq Comp]
    {K L : Comp → Type} [∀ e, Fintype (K e)] [∀ e, Fintype (L e)]
    [DecidableEq Draw] [DecidableEq B] [DecidableEq H] [DecidableEq N]
    {E : Matrix B B Binary} [Nonempty (Frame B H N E)]
    (hN : 2 * (Fintype.card B + Fintype.card H) + 1 ≤ Fintype.card N)
    (C : ∀ e, Matrix (Draw × (B ⊕ H)) (K e) Binary)
    (D : ∀ e, Matrix (Draw × (B ⊕ H)) (L e) Binary)
    (y : ∀ e, Matrix N (K e) Binary) (z : ∀ e, Matrix N (L e) Binary) :
    (PMF.uniformOfFintype (Draw → Comp → Frame B H N E)).toOuterMeasure
      {o | ∀ e, plusImages (C e) (fun i => o i e) = y e ∧ minusImages (D e) (fun i => o i e) = z e} ≤
      (4 : ℝ≥0∞) ^ (Fintype.card Draw * Fintype.card Comp) /
        2 ^ (Fintype.card N * ∑ e, (C e).rank +
          (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H)) * ∑ e, (D e).rank) := by
  classical
  let swap : (Comp → Draw → Frame B H N E) ≃ (Draw → Comp → Frame B H N E) := {
    toFun := fun o i e => o e i
    invFun := fun o e i => o i e
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let obs (e : Comp) (o : Draw → Frame B H N E) := (plusImages (C e) o, minusImages (D e) o)
  have hp : (PMF.uniformOfFintype (Draw → Comp → Frame B H N E)).toOuterMeasure
      {o | ∀ e, plusImages (C e) (fun i => o i e) = y e ∧ minusImages (D e) (fun i => o i e) = z e} =
      ∏ e, (PMF.uniformOfFintype (Draw → Frame B H N E)).toOuterMeasure
        {o | plusImages (C e) o = y e ∧ minusImages (D e) o = z e} := by
    rw [← FiniteUniform.map_equiv swap, PMF.toOuterMeasure_map_apply]
    have hmap := FiniteUniform.map_pi_apply obs (fun e => (y e, z e))
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply] at hmap
    have he : (fun o e => obs e (o e)) ⁻¹' {fun e => (y e, z e)} =
        swap ⁻¹' {o | ∀ e, plusImages (C e) (fun i => o i e) = y e ∧
          minusImages (D e) (fun i => o i e) = z e} := by
      ext o
      simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Prod.mk.injEq,
        Set.mem_ofPred_eq, obs, swap, Equiv.coe_fn_mk]
    rw [he] at hmap
    rw [hmap]
    apply Finset.prod_congr rfl
    intro e _
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext o
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, obs, Prod.mk.injEq]
  rw [hp]
  calc
    _ ≤ ∏ e, ((4 : ℝ≥0∞) ^ Fintype.card Draw /
        2 ^ (Fintype.card N * (C e).rank + (D e).rank *
          (Fintype.card N - Fintype.card Draw * (Fintype.card B + Fintype.card H)))) :=
      Finset.prod_le_prod' (fun e _ => Lax342547.ReferenceImages.joint_rank_cap hN (C e) (D e) (y e) (z e))
    _ = _ := by
      rw [ENNReal.prod_div_distrib_of_ne_top (by intro e _; simp),
        Finset.prod_const, Finset.card_univ, ← pow_mul, Finset.prod_pow_eq_pow_sum]
      congr 2
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm]

end Lax342547Proofs.ReferenceImages
