import Lax342547.ComponentSpaces
import Lax342547Proofs.CoverClasses
import Lax342547Proofs.DirectRanks

namespace Lax342547Proofs.ComponentSpaces
open Lax342547.ComponentSpaces

set_option backward.isDefEq.respectTransparency false
open Lax342547.CoverClasses
open scoped BigOperators

/--
---
conclusion: Lax342547.ComponentSpaces.coordinate_space_bot
---
-/
theorem coordinate_space_bot {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] :
    coordinateSpace (fun i => (⊥ : Submodule K (V i))) = ⊥ := by
  ext v
  change (∀ i, v i = 0) ↔ v = 0
  exact ⟨fun h => funext h,fun h i => congrFun h i⟩

/--
---
conclusion: Lax342547.ComponentSpaces.coordinate_space_sup
---
-/
theorem coordinate_space_sup {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (S T : ∀ i, Submodule K (V i)) :
    coordinateSpace S ⊔ coordinateSpace T = coordinateSpace (fun i => S i ⊔ T i) := by
  classical
  apply le_antisymm
  · apply sup_le
    · intro v hv i
      exact (show S i ≤ S i ⊔ T i from le_sup_left) (hv i)
    · intro v hv i
      exact (show T i ≤ S i ⊔ T i from le_sup_right) (hv i)
  · intro v hv
    have hex : ∀ i, ∃ s ∈ S i, ∃ t ∈ T i, s+t=v i := fun i => Submodule.mem_sup.mp (hv i)
    choose s hs t ht he using hex
    refine Submodule.mem_sup.mpr ⟨s,hs,t,ht,?_⟩
    exact funext he

/--
---
conclusion: Lax342547.ComponentSpaces.componentwise_join_closed
---
-/
theorem componentwise_join_closed {K e : Type} [Field K] {V : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] : JoinClosed (Componentwise (K := K) (V := V)) := by
  constructor
  · exact ⟨fun i => ⊥,coordinate_space_bot.symm⟩
  · rintro S T ⟨A,rfl⟩ ⟨B,rfl⟩
    exact ⟨fun i => A i ⊔ B i,coordinate_space_sup A B⟩

/--
---
conclusion: Lax342547.ComponentSpaces.diagonal_range
---
-/
theorem diagonal_range {K e : Type} [Field K] {V W : e → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)] (M : ∀ i, V i →ₗ[K] W i) :
    LinearMap.range (LinearMap.piMap M) = coordinateSpace (fun i => LinearMap.range (M i)) := by
  classical
  apply le_antisymm
  · rintro v ⟨x,rfl⟩ i
    exact LinearMap.mem_range_self (M i) (x i)
  · intro v hv
    choose x hx using hv
    exact ⟨x,funext hx⟩

end Lax342547Proofs.ComponentSpaces
