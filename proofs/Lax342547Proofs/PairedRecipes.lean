import Lax342547.PairedRecipes
import Lax342547Proofs.ConcreteRecipes

namespace Lax342547Proofs.PairedRecipes

set_option backward.isDefEq.respectTransparency false

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.WitnessAtoms
open Lax342547.PairedWitnesses Lax342547.ConcreteRecipes Lax342547.PairedRecipes
open Lax342547.ExactPins Lax342547.SmallTables Lax342547.TableContractions

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n}

/--
---
conclusion: Lax342547.PairedRecipes.endpoint_fresh
---
The disjoint sum of the two lists is the same family of positions as the
dependent endpoint index in the freshness condition. Thus distinct atom
indices really have distinct selector labels.
-/
theorem endpoint_fresh (W : Lists k n b degree r hr) (i : Fin 2) :
    Function.Injective (fun x : Position W i => (endpointAtoms W i x).label) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      have he := W.left_fresh i (a₁ := ⟨0, x⟩) (a₂ := ⟨0, y⟩) h
      exact congrArg Sum.inl (eq_of_heq (Sigma.mk.inj_iff.mp he).2)
    | inr y =>
      have he := W.left_fresh i (a₁ := ⟨0, x⟩) (a₂ := ⟨1, y⟩) h
      have := congrArg Sigma.fst he
      norm_num at this
  | inr x =>
    cases y with
    | inl y =>
      have he := W.left_fresh i (a₁ := ⟨1, x⟩) (a₂ := ⟨0, y⟩) h
      have := congrArg Sigma.fst he
      norm_num at this
    | inr y =>
      have he := W.left_fresh i (a₁ := ⟨1, x⟩) (a₂ := ⟨1, y⟩) h
      exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj_iff.mp he).2)

variable {H N : Type} [Fintype H] [Fintype N] {E : Moment k n b degree}

/--
---
conclusion: Lax342547.PairedRecipes.flip_recipe
---
Reverse the matched positions and the two cross tables. Matched diagonal
bits transfer oddness; role parity is symmetric; the effective and coupled
equations exchange their left and right roles exactly.
-/
theorem flip_recipe (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    {P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N}
    (T : Table P Q) (A B : Fin 2 → Finset (Fin b → Binary))
    (h : ScalarRecipe W D L R oA oB T A B) :
    ScalarRecipe (flip W) D L R oB oA (flipTable T) B A := by
  refine ⟨⟨fun i z t => h.fresh.2 z i t, fun i z t => h.fresh.1 z i t⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i z
    change (∑ t, diagonalBit hr (W.right z i t)) = 1
    simpa only [← W.same_diagonal] using h.odd z i
  · intro i z
    change D.role (rightWitness W z i) + D.role (leftWitness W z i) = 1
    rw [add_comm]
    exact h.roles z i
  · intro i z x
    exact h.effectiveRight z i x
  · intro i z x
    exact h.effectiveLeft z i x
  · intro i z
    exact h.coupledRight z i
  · intro i z
    exact h.coupledLeft z i

theorem endpoint_prescriptions (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (hk : 0 < k) (hcopies : 0 < copies)
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    {P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N}
    (T : Table P Q) (A B : Fin 2 → Finset (Fin b → Binary))
    (h : ScalarRecipe W D L R oA oB T A B) : Prescriptions W D oB copies := by
  intro i
  let : Nonempty (Fin (W.length i 0)) := ⟨⟨0, by have := W.positive i 0; omega⟩⟩
  let : Nonempty (Fin (W.length i 1)) := ⟨⟨0, by have := W.positive i 1; omega⟩⟩
  let data := fun x : Position W i => (endpointAtoms W i x).numerical hr
  let opposite : Position W i → Binary := Sum.elim
    (fun t => D.role (W.right i 0 t).profile) (fun t => D.role (W.right i 1 t).profile)
  have ha (x : Position W i) : (data x).role = D.role (endpointAtoms W i x).profile :=
    (WitnessAtoms.atom_testers D (endpointAtoms W i x)).1.symm
  have hrole₁ : (∑ t : Fin (W.length i 0), (data (.inl t)).role) +
      (∑ t : Fin (W.length i 0), opposite (.inl t)) = 1 := by
    simpa only [ha, opposite, endpointAtoms, Sum.elim_inl, leftWitness, rightWitness, map_sum]
      using h.roles i 0
  have hrole₂ : (∑ t : Fin (W.length i 1), (data (.inr t)).role) +
      (∑ t : Fin (W.length i 1), opposite (.inr t)) = 1 := by
    simpa only [ha, opposite, endpointAtoms, Sum.elim_inr, leftWitness, rightWitness, map_sum]
      using h.roles i 1
  have hcoupled : (∑ t : Fin (W.length i 0),
      (oppositeP W oB i (.inl t) + opposite (.inl t))) =
      ∑ t : Fin (W.length i 1), (oppositeP W oB i (.inr t) + opposite (.inr t)) := by
    have hc := h.coupledRight i 0
    change (ownContraction oB 0 + D.role) (rightWitness W i 0) =
      (ownContraction oB 1 + D.role) (rightWitness W i 1) at hc
    simpa only [oppositeP, opposite, Sum.elim_inl, Sum.elim_inr, rightWitness,
      map_sum, LinearMap.add_apply] using hc
  obtain ⟨lbits, rbits, hzero, hbits⟩ := ConcreteRecipes.prescribe hk hcopies data opposite
    (oppositeP W oB i) hrole₁ hrole₂ hcoupled
  refine ⟨lbits, rbits, hzero, ?_⟩
  intro L' R' htest
  exact hbits n b degree r hr D L' R' (endpointAtoms W i) (fun _ => rfl) htest

/--
---
conclusion: Lax342547.PairedRecipes.paired_prescriptions
---
At either endpoint the opposite coupled equation supplies the row-sum
compatibility. Apply the numerical prescription theorem, then repeat for
the reversed unit roles. The resulting four prescriptions concern only
distinct atoms and imply the full selected-atom gradient identities.
-/
theorem paired_prescriptions (W : Lists k n b degree r hr)
    (D : Testers (k := k) (b := b) (degree := degree) hr) {copies : ℕ}
    (hk : 0 < k) (hcopies : 0 < copies)
    (L R : Fin copies → Component (Tag k) → Component (Tag k) → Moment k n b degree)
    (oA oB : Unit (H := H) (N := N) (E := E))
    {P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N}
    (T : Table P Q) (A B : Fin 2 → Finset (Fin b → Binary))
    (h : ScalarRecipe W D L R oA oB T A B) :
    Prescriptions W D oB copies ∧ Prescriptions (flip W) D oA copies := by
  exact ⟨endpoint_prescriptions W D hk hcopies L R oA oB T A B h,
    endpoint_prescriptions (flip W) D hk hcopies L R oB oA (flipTable T) B A
      (flip_recipe W D L R oA oB T A B h)⟩

end Lax342547Proofs.PairedRecipes
