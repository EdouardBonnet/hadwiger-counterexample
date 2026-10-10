import Lax342547.FrozenRecords
import Lax342547Proofs.FrozenCharacters
import Lax342547Proofs.RawFrames

namespace Lax342547Proofs.FrozenRecords
open Lax342547.FrozenRecords

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace Lax342547.ConcreteGeometry

/--
---
conclusion: Lax342547.FrozenRecords.record_count
---
-/
theorem record_count {I X : Type} [Fintype I] [Fintype X] : by
    classical
    exact Fintype.card (Matrix I X Binary) = 2 ^ (Fintype.card I * Fintype.card X) := by
  classical
  simp [Matrix, ZMod.card, ← pow_mul, Nat.mul_comm]

/--
---
conclusion: Lax342547.FrozenRecords.record_evaluation
---
-/
theorem record_evaluation {I X N : Type} [Fintype I] [Fintype N]
    (A : (I → Binary) →ₗ[Binary] (N → Binary)) (frozen : X → N → Binary)
    (v : I → Binary) (x : X) :
    dotProduct (A v) (frozen x) = ∑ i, v i * record A frozen i x := by
  classical
  have hv : v = ∑ i, v i • Pi.single i (1 : Binary) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  rw [sum_dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_dotProduct]
  rfl

/--
---
conclusion: Lax342547.FrozenRecords.records_determine_frozen
---
-/
theorem records_determine_frozen {I X N : Type} [Fintype I] [Fintype N]
    (A A' : (I → Binary) →ₗ[Binary] (N → Binary)) (frozen : X → N → Binary)
    (hrec : record A frozen = record A' frozen) (v : I → Binary)
    (w : Submodule.span Binary (Set.range frozen)) :
    dotProduct (A v) w.val = dotProduct (A' v) w.val := by
  have hgen (x : X) : dotProduct (A v) (frozen x) = dotProduct (A' v) (frozen x) := by
    rw [record_evaluation, record_evaluation, hrec]
  have heq : ∀ w ∈ Submodule.span Binary (Set.range frozen),
      dotProduct (A v) w = dotProduct (A' v) w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨x, rfl⟩ := hw; exact hgen x
    | zero => simp
    | add w w' hw hw' ih ih' => simp only [dotProduct_add, ih, ih']
    | smul c w hw ih => simp only [dotProduct_smul, ih]
  exact heq w.val w.property

/--
---
conclusion: Lax342547.FrozenRecords.two_records_cross_agreement
---
-/
theorem two_records_cross_agreement {I J X Y N : Type}
    [Fintype I] [Fintype J] [Fintype N]
    (A A' : (I → Binary) →ₗ[Binary] (N → Binary))
    (B B' : (J → Binary) →ₗ[Binary] (N → Binary))
    (left : X → I → Binary) (right : Y → J → Binary)
    (leftImages : X → N → Binary) (rightImages : Y → N → Binary)
    (hleft : ∀ x, A (left x) = leftImages x ∧ A' (left x) = leftImages x)
    (hright : ∀ y, B (right y) = rightImages y ∧ B' (right y) = rightImages y)
    (hrecA : record A rightImages = record A' rightImages)
    (hrecB : record B leftImages = record B' leftImages) :
    (∀ v ∈ Submodule.span Binary (Set.range left), ∀ w,
      dotProduct (A v) (B w) = dotProduct (A' v) (B' w)) ∧
    (∀ v w, w ∈ Submodule.span Binary (Set.range right) →
      dotProduct (A v) (B w) = dotProduct (A' v) (B' w)) := by
  have hpointL (x : X) (w : J → Binary) :
      dotProduct (A (left x)) (B w) = dotProduct (A' (left x)) (B' w) := by
    rw [(hleft x).1, (hleft x).2, dotProduct_comm (leftImages x), dotProduct_comm (leftImages x)]
    rw [record_evaluation, record_evaluation, hrecB]
  have hpointR (v : I → Binary) (y : Y) :
      dotProduct (A v) (B (right y)) = dotProduct (A' v) (B' (right y)) := by
    rw [(hright y).1, (hright y).2, record_evaluation, record_evaluation, hrecA]
  constructor
  · intro v hv w
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨x, rfl⟩ := hv; exact hpointL x w
    | zero => simp
    | add v v' hv hv' ih ih' => simp only [map_add, add_dotProduct, ih, ih']
    | smul c v hv ih => simp only [map_smul, smul_dotProduct, ih]
  · intro v w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨y, rfl⟩ := hw; exact hpointR v y
    | zero => simp
    | add w w' hw hw' ih ih' => simp only [map_add, dotProduct_add, ih, ih']
    | smul c w hw ih => simp only [map_smul, dotProduct_smul, ih]

end Lax342547Proofs.FrozenRecords
