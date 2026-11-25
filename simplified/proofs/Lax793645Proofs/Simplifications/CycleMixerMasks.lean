import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.MixerConditions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped BigOperators Classical
noncomputable section
variable {g : ℕ}

/-- The vertex at the start of an oriented cycle component. -/
def cycleOrigin (e : Comp g) : Tag g :=
  if h : 3≤g then (CycleGeometry.forwardEquiv h).symm e else e.val.1

theorem cycle_origin_forward (hg : 3≤g) (l : Tag g) :
    cycleOrigin (CycleGeometry.forward (by omega : 2≤g) l)=l := by
  simp only [cycleOrigin,dif_pos hg]
  exact (CycleGeometry.forwardEquiv hg).symm_apply_apply l

theorem cycle_forward_origin (hg : 3≤g) (e : Comp g) :
    CycleGeometry.forward (by omega : 2≤g) (cycleOrigin e)=e := by
  simp only [cycleOrigin,dif_pos hg]
  exact (CycleGeometry.forwardEquiv hg).apply_symm_apply e

def cycleWeight (e f : Comp g) : F :=
  if h : 2≤g then ∑ i : Fin ((g-1)/2),
    if CycleGeometry.forward h (CycleGeometry.matchingVertex (cycleOrigin e) i)=f then 1 else 0
  else 0

def cycleAggregate {V : Type*} [AddCommGroup V] [Module F V]
    (e : Comp g) : (Comp g→V)→ₗ[F]V := CycleGeometry.matchingMap (cycleOrigin e)

theorem cycle_aggregate_sum {V : Type*} [AddCommGroup V] [Module F V]
    (e : Comp g) (x : Comp g→V) : cycleAggregate e x=∑ f,cycleWeight e f •x f := by
  by_cases hg : 2≤g
  · simp only [cycleAggregate,CycleGeometry.matchingMap,LinearMap.sum_apply,
      CycleGeometry.outgoingMap,dif_pos hg,LinearMap.proj_apply,cycleWeight,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro i _
    simp only [ite_smul,one_smul,zero_smul]
    simp
  simp only [cycleAggregate,CycleGeometry.matchingMap,LinearMap.sum_apply,
    CycleGeometry.outgoingMap,dif_neg hg,LinearMap.zero_apply,cycleWeight,
    zero_smul,sum_const_zero]

theorem cycle_aggregate_cut {V : Type*} [AddCommGroup V] [Module F V]
    (hg : Odd g) (e : Comp g) (w : Tag g→V) :
    cycleAggregate e (CycleGeometry.cut w)=(∑ l,w l)+w (cycleOrigin e) :=
  CycleGeometry.matchingMap_cut hg w (cycleOrigin e)

theorem matching_vertex_injective (t : Tag g) :
    Injective (CycleGeometry.matchingVertex t) := by
  intro i j h
  have he:=congrArg Fin.val (add_right_cancel h)
  apply Fin.ext
  dsimp only [CycleGeometry.matchingVertex] at he
  omega

theorem cycle_weight_exists (hg : 3≤g) (e : Comp g) : ∃ f,cycleWeight e f=1 := by
  let i : Fin ((g-1)/2):=⟨0,by omega⟩
  let f:=CycleGeometry.forward (by omega : 2≤g) (CycleGeometry.matchingVertex (cycleOrigin e) i)
  refine ⟨f,?_⟩
  simp only [cycleWeight,dif_pos (show 2≤g by omega)]
  rw [sum_eq_single i]
  · simp [f]
  · intro j _ hji
    rw [if_neg]
    intro h
    exact hji (matching_vertex_injective _ (CycleGeometry.forward_injective hg h))
  simp

theorem cycle_weight_matching (hg : 3≤g) (e : Comp g) (i : Fin ((g-1)/2)) :
    cycleWeight e (CycleGeometry.forward (by omega : 2≤g)
      (CycleGeometry.matchingVertex (cycleOrigin e) i))=1 := by
  simp only [cycleWeight,dif_pos (show 2≤g by omega)]
  rw [sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg]
    intro h
    exact hji (matching_vertex_injective _ (CycleGeometry.forward_injective hg h))
  simp

theorem cycle_weight_next (hg : 3≤g) (t : Tag g) :
    cycleWeight (CycleGeometry.forward (by omega : 2≤g) t)
      (CycleGeometry.forward (by omega : 2≤g) (CycleGeometry.next t))=1 := by
  let i : Fin ((g-1)/2):=⟨0,by omega⟩
  have he : CycleGeometry.matchingVertex t i=CycleGeometry.next t := by
    haveI : NeZero g:=⟨by omega⟩
    rw [CycleGeometry.next_eq_add]
    change (⟨2*0+1,by omega⟩ : Fin g)+t=t+1
    rw [add_comm]
    congr 1
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (show 1<g by omega)]
  simpa only [cycle_origin_forward hg,he] using
    cycle_weight_matching hg (CycleGeometry.forward (by omega : 2≤g) t) i

/-- One representative suffices to store the matrix for a whole matching. -/
def cycleAnchor (e : Comp g) : Comp g :=
  if hg : 3≤g then (cycle_weight_exists hg e).choose else e

theorem cycle_weight_anchor (hg : 3≤g) (e : Comp g) :
    cycleWeight e (cycleAnchor e)=1 := by
  simp only [cycleAnchor,dif_pos hg]
  exact (cycle_weight_exists hg e).choose_spec

theorem cycle_weight_star (hg : Odd g) (e : Comp g) (l : Tag g) :
    (∑ f,if inc f l then cycleWeight e f else 0)=if cycleOrigin e=l then 0 else 1 := by
  let w : Tag g→F:=Pi.single l 1
  have hc : CycleGeometry.cut w=fun f=>if inc f l then (1:F) else 0 := by
    funext f
    have hne : f.val.1≠f.val.2:=ne_of_lt f.property.1
    by_cases h₁:f.val.1=l
    · have h₂:f.val.2≠l:=fun h₂=>hne (h₁.trans h₂.symm)
      simp [CycleGeometry.cut,w,inc,CycleGeometry.inc,h₁,h₂]
    by_cases h₂:f.val.2=l
    · simp [CycleGeometry.cut,w,inc,CycleGeometry.inc,h₁,h₂]
    simp [CycleGeometry.cut,w,inc,CycleGeometry.inc,h₁,h₂]
  have hh:=cycle_aggregate_cut hg e w
  rw [cycle_aggregate_sum,hc] at hh
  simp only [smul_eq_mul,mul_ite,mul_one,mul_zero] at hh
  rw [hh]
  by_cases he:cycleOrigin e=l
  · simp [w,he,char_two]
  simp [w,he]

end
end Lax793645Proofs.Simplifications
