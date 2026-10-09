import Lax342547.Atoms
import Lax342547Proofs.ConcreteCut

namespace Lax342547Proofs.Atoms

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.CutProfiles Lax342547.ConcreteCut Lax342547.Atoms

variable {k n b degree r : ℕ}

/--
---
conclusion: Lax342547.Atoms.atom_component
---
Apply the cut map to the representation supported only at l. Its sum
over an unordered pair is the point moment precisely when l is incident.
-/
theorem atom_component (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) (e : Component (Tag k)) :
    (atom (degree := degree) l s z hz).val e = if l ∈ e.val then pointMoment selectorEval s z else 0 := by
  classical
  change (∑ t ∈ e.val, Pi.single l (pointMoment selectorEval s z) t) = _
  simp [Pi.single_apply]

/--
---
conclusion: Lax342547.Atoms.flavor_coordinates
---
Each ordinary block is intersected with the allowed tag blocks. The
generic and shared-only flavors retain all common coordinates; a pure
flavor removes just S among those coordinates.
-/
theorem flavor_coordinates (l : Tag k) (f : Flavor k) :
    retained (n := n) l f ⊆ allowedBase k n l ∧
      (∀ i : Fin n, sharp i ∈ retained l f) ∧ (∀ i : Fin n, free i ∈ retained l f) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (⟨⟨d, t⟩, i⟩ | ⟨q, i⟩) hi
    · exact hi.1
    · trivial
  · intro i
    cases f with
    | generic => trivial
    | sharedOnly => trivial
    | pure _ => change (1 : Fin 3) ≠ 0; decide
  · intro i
    cases f with
    | generic => trivial
    | sharedOnly => trivial
    | pure _ => change (2 : Fin 3) ≠ 0; decide

theorem parameterValue_allowed {l : Tag k} {f : Flavor k} (p : Parameters n l f) :
    ∀ i, i ∉ allowedBase k n l → parameterValue p i = 0 := by
  classical
  intro i hi
  have hn : i ∉ retained l f := fun h => hi ((flavor_coordinates l f).1 h)
  simp [parameterValue, hn]

theorem atom_role {hr : 2 * r ≤ n} (D : Testers (k := k) (b := b) (degree := degree) hr)
    (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) :
    D.role (atom l s z hz) = etaO (degree := degree) hr (pointMoment selectorEval s z) := by
  classical
  rw [atom, ConcreteCut.role_formula]
  simp [atomRepresentation, Pi.single_apply, apply_ite]

theorem atom_diagonal (hr : 2 * r ≤ n) (l : Tag k) (s : Fin b → Binary) (z : Base k n → Binary)
    (hz : ∀ i, i ∉ allowedBase k n l → z i = 0) :
    chiStar (degree := degree) hr (atomRepresentation l s z hz) =
      eta (degree := degree) hr (pointMoment selectorEval s z) := by
  classical
  simp [chiStar, representativeAt, atomRepresentation, Pi.single_apply, apply_ite, LinearMap.sum_apply]

/--
---
conclusion: Lax342547.Atoms.parameterLaw_product
---
The uniform mass on the finite bit-function space is the product of the
uniform masses of its retained coordinate bits.
-/
theorem parameterLaw_product (l : Tag k) (f : Flavor k) (p : Parameters n l f) :
    parameterLaw n l f p = ∏ i : {i : Base k n // i ∈ retained l f}, PMF.uniformOfFintype Binary (p i) := by
  classical
  simp [parameterLaw, PMF.uniformOfFintype_apply, ENNReal.inv_pow, Parameters]

end Lax342547Proofs.Atoms
