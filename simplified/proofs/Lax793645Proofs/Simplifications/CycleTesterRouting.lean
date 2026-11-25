import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.QuadraticTesters

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Finset LinearMap
open scoped BigOperators
noncomputable section
namespace CycleTesterRouting
variable {p : Shape} {n : ℕ}

theorem edge_eq_iff {g : ℕ} (l d : Fin g) (h : (SimpleGraph.cycleGraph g).Adj l d)
    (e : CycleGeometry.Comp g) :
    CycleGeometry.edge l d h=e ↔
      (l=e.val.1 ∧ d=e.val.2) ∨ (l=e.val.2 ∧ d=e.val.1) := by
  constructor
  · intro he
    unfold CycleGeometry.edge at he
    split_ifs at he with hlt
    · exact Or.inl ⟨congrArg (fun e => e.val.1) he,congrArg (fun e => e.val.2) he⟩
    · exact Or.inr ⟨congrArg (fun e => e.val.2) he,congrArg (fun e => e.val.1) he⟩
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact CycleGeometry.edge_eq e.property.1 h
    · rw [CycleGeometry.edge_symm,CycleGeometry.edge_eq e.property.1]

theorem outgoing_single (l : Tag p.g) (e : Comp p.g) (M : Moment p n) :
    CycleGeometry.outgoingMap l (Pi.single e M)=
      (if l=e.val.1 ∧ CycleGeometry.next l=e.val.2 then M else 0)+
      (if l=e.val.2 ∧ CycleGeometry.next l=e.val.1 then M else 0) := by
  classical
  have hg : 2≤p.g := by
    have hlt : e.val.1.val<e.val.2.val := e.property.1
    have := e.val.2.isLt
    omega
  rw [CycleGeometry.outgoingMap,dif_pos hg]
  change (Pi.single e M : Profile p n) (CycleGeometry.forward hg l)=_
  have he := edge_eq_iff l (CycleGeometry.next l) (CycleGeometry.adjacent_next hg l) e
  change CycleGeometry.forward hg l=e ↔ _ at he
  by_cases h1 : l=e.val.1 ∧ CycleGeometry.next l=e.val.2
  · have h2 : ¬(l=e.val.2 ∧ CycleGeometry.next l=e.val.1) :=
      fun h => e.property.1.ne (h1.1.symm.trans h.1)
    rw [(he.mpr (Or.inl h1)),Pi.single_eq_same,if_pos h1,if_neg h2,add_zero]
  by_cases h2 : l=e.val.2 ∧ CycleGeometry.next l=e.val.1
  · rw [(he.mpr (Or.inr h2)),Pi.single_eq_same,if_neg h1,if_pos h2,zero_add]
  have hh : CycleGeometry.forward hg l≠e := fun h => (he.mp h).elim h1 h2
  rw [Pi.single_eq_of_ne hh,if_neg h1,if_neg h2,add_zero]

def routed (p : Shape) (n : ℕ) (t a b : Tag p.g) : Moment p n :=
  if CycleGeometry.next a=b then testM p n (Block.O a t) else 0

theorem role_at (t : Tag p.g) (e : Comp p.g) (M : Moment p n) :
    roleT p n t (Pi.single e M)=
      mpair (routed p n t e.val.1 e.val.2+routed p n t e.val.2 e.val.1) M := by
  classical
  simp only [roleT,LinearMap.sum_apply,LinearMap.comp_apply,outgoing_single,map_add,
    Finset.sum_add_distrib,mpair_add]
  have hi (a b : Tag p.g) :
      (∑ l,etab p n (Block.O l t) (if l=a ∧ CycleGeometry.next l=b then M else 0))=
        mpair (routed p n t a b) M := by
    rw [Finset.sum_eq_single a]
    · by_cases h : CycleGeometry.next a=b
      · simp [h,routed,etab]
      · simp [h,routed,map_zero,mpair_comm]
    · intro l _ hl; simp [hl,map_zero]
    · simp
  exact congrArg₂ (·+·) (hi _ _) (hi _ _)

/-- The matching contributes one scalar multiple of the shared tester at
any component, irrespective of how many deleted-vertex matchings use it. -/
def sharedWeight (p : Shape) (t : Tag p.g) (e : Comp p.g) : F :=
  ∑ i : Fin ((p.g-1)/2),
    if h : 2≤p.g then
      if CycleGeometry.forward h (CycleGeometry.matchingVertex t i)=e then 1 else 0
    else 0

theorem shared_at (t : Tag p.g) (e : Comp p.g) (M : Moment p n) :
    sharedT p n t (Pi.single e M)=sharedWeight p t e*etab p n Block.S M := by
  classical
  have hg : 2≤p.g := by
    have hlt : e.val.1.val<e.val.2.val := e.property.1
    have := e.val.2.isLt
    omega
  simp only [sharedT,LinearMap.comp_apply,CycleGeometry.matchingMap,LinearMap.sum_apply,
    map_sum,sharedWeight,Finset.sum_mul,CycleGeometry.outgoingMap,dif_pos hg]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : CycleGeometry.forward hg (CycleGeometry.matchingVertex t i)=e
  · simp [hi]
  · simp [hi,Pi.single_eq_of_ne hi]

end CycleTesterRouting
end
end Lax793645Proofs.Simplifications
