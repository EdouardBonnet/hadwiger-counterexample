import Lax342547.WitnessAtoms
import Lax342547Proofs.Atoms
import Lax342547.UnaryMixer

namespace Lax342547Proofs.WitnessAtoms

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.Atoms Lax342547.WitnessAtoms

/--
---
conclusion: Lax342547.WitnessAtoms.tester_properties
---
The cross tester terms occur with their transposes. They cancel on the
diagonal in characteristic two, and each binary role bit squares to itself.
-/
theorem tester_properties {k : ℕ} :
    (∀ x y : Numerical k, testerEntry x y = testerEntry y x) ∧
      ∀ x : Numerical k, testerEntry x x = x.role := by
  constructor
  · intro x y
    unfold testerEntry
    rw [mul_comm x.role y.role]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ring
  · intro x
    have hs : (∑ t, (x.aTag t * x.bTag t + x.bTag t * x.aTag t)) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [mul_comm (x.bTag t), ZModModule.add_self]
    rw [testerEntry, hs, add_zero]
    have hb (v : Binary) : v * v = v := by fin_cases v <;> rfl
    exact hb x.role

/--
---
conclusion: Lax342547.WitnessAtoms.atom_testers
---
The actual descended tester evaluations on a point atom are precisely
the sums and tag-dependent shared bit in its numerical tester record.
-/
theorem atom_testers {k n b degree r : ℕ} {hr : 2 * r ≤ n}
    (D : Testers (k := k) (b := b) (degree := degree) hr) (x : PointAtom k n b degree) :
    D.role x.profile = (x.numerical hr).role ∧
      (∀ t, D.aTag t x.profile = (x.numerical hr).aTag t) ∧
      ∀ t, D.bTag t x.profile = (x.numerical hr).bTag t := by
  have ha (t : Tag k) : D.aTag t x.profile = (x.numerical hr).aTag t :=
    Atoms.atom_aTag D x.tag x.label x.base x.supported t
  refine ⟨?_, ha, ?_⟩
  · simp only [Testers.role, LinearMap.sum_apply, ha, Numerical.role]
  · intro t
    exact Atoms.atom_bTag D x.tag x.label x.base x.supported t

/--
---
conclusion: Lax342547.WitnessAtoms.allowed_index
---
Every tag has 2k incident components. Choose one for each star and any
of the J mixer copies to obtain an allowed ordered product index.
-/
theorem allowed_index {k J : ℕ} (hk : 0 < k) (hJ : 0 < J) (x y : Numerical k) :
    ∃ t : ProductIndex k J, allowedIndex x y t := by
  classical
  have hexists (l : Tag k) : (Lax342547.UnaryMixer.incident l).Nonempty := by
    apply Finset.card_pos.mp
    rw [Lax342547.UnaryMixer.incident_card]
    omega
  obtain ⟨e, he⟩ := hexists x.tag
  obtain ⟨f, hf⟩ := hexists y.tag
  refine ⟨(⟨0, hJ⟩, e, f), ?_⟩
  exact ⟨(Finset.mem_filter.mp he).2, (Finset.mem_filter.mp hf).2⟩

end Lax342547Proofs.WitnessAtoms
