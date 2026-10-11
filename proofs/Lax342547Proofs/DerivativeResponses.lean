import Lax342547.DerivativeResponses
import Lax342547Proofs.DerivativeContractions
import Lax342547Proofs.PureObstructions
import Lax342547Proofs.FrozenValues
import Lax342547.Atoms
import Lax342547.BarredSpaces
import Lax342547.ChannelChanges
import Lax342547.DerivativeContractions
import Lax342547.PrimalContractions
import Lax342547.PureObstructions
import Lax342547.ResidualLabels
import Lax342547.SelectedRemoval
import Lax342547.TensorContractions

namespace Lax342547Proofs.DerivativeResponses

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.TableSpaces Lax342547.PairedAnnihilators
open Lax342547.BarredSpaces Lax342547.ChannelChanges Lax342547.TableContractions
open Lax342547.DerivativeResponses Lax342547.SelectedRemoval

set_option backward.isDefEq.respectTransparency false

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type} [Fintype H]

theorem restriction_zero {B : Type} (D : Submodule Binary (Nominal B H))
    (S : Submodule Binary (H → Binary)) (i : Fin 2) : restriction D S 0 i = 0 := by
  ext v h
  simp [restriction]

theorem component_zero {Comp B : Type} [Fintype B]
    (F : CrossForms Comp B H) (e : Comp) (z : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary)) :
    componentResponse F e z D E S T 0 0 = 0 := by
  simp [componentResponse, restriction_zero, DerivativeContractions.ambient_zero_left,
    DerivativeContractions.ambient_zero_right]

theorem response_zero (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2) :
    response W P Q U V F z 0 0 = 0 := by
  simp [response, component_zero]

omit [Fintype H] in
theorem pure_zero (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary)) :
    Lax342547.PureObstructions.response W P U V 0 = 0 := by
  simp [Lax342547.PureObstructions.response, PureObstructions.pureResponse_zero]

/--
---
conclusion: Lax342547.DerivativeResponses.pure_annihilation
---
Set both allowed derivative families to zero to recover every pure
quotient response from full response annihilation.
-/
theorem pure_annihilation (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x) :
    Lax342547.PureObstructions.Annihilates W P U V x := by
  intro β
  have hh := h β 0 0
  simpa only [fullResponse, response_zero, add_zero] using hh

/--
---
conclusion: Lax342547.DerivativeResponses.derivative_annihilation
---
Set the arbitrary pure bilinear family to zero to recover every
allowed derivative response from full response annihilation.
-/
theorem derivative_annihilation (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (δF : PlusParameters W P Q U z) (δG : MinusParameters W P Q V z) :
    response W P Q U V F z δF δG x = 0 := by
  have hh := h 0 δF δG
  simpa only [fullResponse, pure_zero, zero_add] using hh

theorem component_single {Comp B : Type} [Fintype B]
    (F : CrossForms Comp B H) (e : Comp) (z i : Fin 2)
    (D E : Submodule Binary (Nominal B H)) (S T : Submodule Binary (H → Binary))
    (δF : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S)
    (δG : (Nominal B H ⧸ E) →ₗ[Binary] perpendicular T) (M : Matrix B B Binary) :
    componentResponse F e z D E S T δF δG (Pi.single i M) =
      Lax342547.TensorContractions.ambient (fullPlus F e i z) (restriction E T δG i) M +
      Lax342547.TensorContractions.ambient (restriction D S δF i) (fullMinus F e i z) M := by
  classical
  simp only [componentResponse, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

theorem restriction_key (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U : Fin 2 → Submodule Binary (H → Binary)) (e : Component (Tag k)) (p : Bool)
    (S : Submodule Binary (H → Binary))
    (δ : (Nominal (Coordinate k n b degree) H ⧸ barred W P U (e, p)) →ₗ[Binary] perpendicular S)
    (i : Fin 2) (u : Σ z, Fin (W.length i z)) (htag : (W.left i u.1 u.2).tag ∈ e.val) :
    restriction (barred W P U (e, p)) S δ i (W.left i u.1 u.2).vector = 0 := by
  have hkey := FrozenValues.key_mem (H := H) W e i u.1 u.2 htag
  have hmem : primalEmbedding (H := H) i (W.left i u.1 u.2).vector ∈ barred W P U (e, p) :=
    (show Lax342547.PairedKeys.keys W e ≤ barred W P U (e, p) from
      le_trans le_sup_right le_sup_left) hkey
  have hz : (barred W P U (e, p)).mkQ
      (primalEmbedding i (W.left i u.1 u.2).vector) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hmem
  change (δ ((barred W P U (e, p)).mkQ
    (primalEmbedding i (W.left i u.1 u.2).vector))).val = 0
  rw [hz, map_zero]
  rfl

theorem derivative_atom (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (δF : PlusParameters W P Q U z) (δG : MinusParameters W P Q V z)
    (i : Fin 2) (u : Σ z, Fin (W.length i z)) :
    response W P Q U V F z δF δG (Pi.single i (W.left i u.1 u.2).profile) = 0 := by
  classical
  simp only [response, LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_eq_zero
  intro e _
  have he : Lax342547.PureObstructions.endpointComponent e
      (Pi.single i (W.left i u.1 u.2).profile) = Pi.single i ((W.left i u.1 u.2).profile.val e) := by
    ext j
    by_cases hji : j = i <;> simp [Lax342547.PureObstructions.endpointComponent, hji]
  rw [he, component_single]
  by_cases htag : (W.left i u.1 u.2).tag ∈ e.val
  · simp only [Lax342547.WitnessAtoms.PointAtom.profile, Lax342547.Atoms.atom_component, htag, if_pos]
    change Lax342547.TensorContractions.ambient _ _
        (Matrix.vecMulVec (W.left i u.1 u.2).vector (W.left i u.1 u.2).vector) +
      Lax342547.TensorContractions.ambient _ _
        (Matrix.vecMulVec (W.left i u.1 u.2).vector (W.left i u.1 u.2).vector) = 0
    rw [Lax342547.TensorContractions.ambient_outer, Lax342547.TensorContractions.ambient_outer,
      restriction_key W P (V e) e false _ (δG e) i u htag,
      restriction_key W P (U e) e true _ (δF e) i u htag]
    simp
  · simp [Lax342547.WitnessAtoms.PointAtom.profile, Lax342547.Atoms.atom_component, htag]

/--
---
conclusion: Lax342547.DerivativeResponses.atom_annihilates
---
Both factors of a selected atom are incident key directions. Its
pure response is zero, and each allowed derivative quotient map also
kills its key input, so the full response is zero.
-/
theorem atom_annihilates (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (i : Fin 2) (u : Σ z, Fin (W.length i z)) :
    Annihilates W P Q U V F z (Pi.single i (W.left i u.1 u.2).profile) := by
  intro β δF δG
  change Lax342547.PureObstructions.response W P U V β _ + response W P Q U V F z δF δG _ = 0
  rw [Lax342547.SelectedRemoval.atom_annihilates W P U V i u β,
    derivative_atom W P Q U V F z δF δG i u, add_zero]

/--
---
conclusion: Lax342547.DerivativeResponses.selected_part_annihilates
---
Expand the actual selected part into endpoint singletons and scalar
multiples of selected atoms; every full response is linear.
-/
theorem selected_part_annihilates (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) :
    Annihilates W P Q U V F z (selectedPart W c) := by
  classical
  intro β δF δG
  rw [← Finset.univ_sum_single (selectedPart W c), map_sum]
  apply Finset.sum_eq_zero
  intro i _
  change fullResponse W P Q U V F z β δF δG
    ((LinearMap.single Binary (fun _ : Fin 2 => Profile k n b degree) i)
      (∑ u, c i u • (W.left i u.1 u.2).profile)) = 0
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro u _
  change c i u • fullResponse W P Q U V F z β δF δG (Pi.single i (W.left i u.1 u.2).profile) = 0
  rw [Lax342547.DerivativeResponses.atom_annihilates W P Q U V F z i u β δF δG, smul_zero]

/--
---
conclusion: Lax342547.DerivativeResponses.subtract_annihilates
---
Linearity and full annihilation of the selected part preserve every
pure and derivative test when selected atoms are subtracted.
-/
theorem subtract_annihilates (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) :
    Annihilates W P Q U V F z (x - selectedPart W c) := by
  intro β δF δG
  rw [map_sub, h β δF δG, Lax342547.DerivativeResponses.selected_part_annihilates W P Q U V F z c β δF δG, sub_self]

/--
---
conclusion: Lax342547.DerivativeResponses.component_annihilation
---
Choose both allowed derivative families supported at the tested
component. Every other component has two zero maps.
-/
theorem component_annihilation (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k))
    (δF : (Nominal (Coordinate k n b degree) H ⧸ barred W P (U e) (e, true)) →ₗ[Binary]
      perpendicular (protectedChannel Q z (e, false)))
    (δG : (Nominal (Coordinate k n b degree) H ⧸ barred W P (V e) (e, false)) →ₗ[Binary]
      perpendicular (protectedChannel Q z (e, true))) :
    componentResponse F e z (barred W P (U e) (e, true))
      (barred W P (V e) (e, false)) (protectedChannel Q z (e, false))
      (protectedChannel Q z (e, true)) δF δG (Lax342547.PureObstructions.endpointComponent e x) = 0 := by
  classical
  have hh := Lax342547.DerivativeResponses.derivative_annihilation W P Q U V F z x h (Pi.single e δF) (Pi.single e δG)
  simp only [response, LinearMap.sum_apply, LinearMap.comp_apply] at hh
  rw [Finset.sum_eq_single e] at hh
  · simpa only [Pi.single_eq_same] using hh
  · intro f _ hfe
    rw [Pi.single_eq_of_ne hfe, Pi.single_eq_of_ne hfe, component_zero, LinearMap.zero_apply]
  · simp

/--
---
conclusion: Lax342547.DerivativeResponses.unselected_obstruction
---
The full obstruction is a pure obstruction, so the checked selected
decomposition supplies bounded unselected blocks. The selected part
also kills the full response, preserving its enlarged annihilation.
-/
theorem unselected_obstruction {K : ℕ} (hk : 0 < k)
    (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (hK : P.rank ≤ K) (A : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A (2 * K + 28))
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (hdegree : 6 * (2 * K + 28) + 4 ≤ degree) :
    ∃ c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary,
    ∃ L : Fin 2 → Component (Tag k) → Finset (Fin b → Binary),
    ∃ Z : Fin 2 → Component (Tag k) → (Fin b → Binary) →
        Matrix (Option (Base k n)) (Option (Base k n)) Binary,
      Annihilates W P Q U V F z (x - selectedPart W c) ∧
      ∀ i e, (L i e).card ≤ 2 * K + 28 ∧
        (∀ s ∈ L i e, s ∉ Lax342547.ResidualLabels.chosenLabels W i ∧
          Lax342547.BaseMoments.IsBaseMoment (Z i e s)) ∧
        (∑ s ∈ L i e, (Z i e s).rank) ≤ 2 * K + 28 ∧
        ((x - selectedPart W c) i).val e =
          ∑ s ∈ L i e, Lax342547.TensorBlocks.block selectorEval s (Z i e s) := by
  obtain ⟨c, L, Z, _, hlabels⟩ := Lax342547.ResidualLabels.unselected_obstruction hk W P hK A hA hfresh
    U V x (Lax342547.DerivativeResponses.pure_annihilation W P Q U V F z x h) hdegree
  exact ⟨c, L, Z, Lax342547.DerivativeResponses.subtract_annihilates W P Q U V F z x h c, hlabels⟩

/--
---
conclusion: Lax342547.DerivativeResponses.right_test
---
Extend the individual minus functional by zero on the other primal
endpoint and both channel blocks, and descend through the actual barred
quotient. Multiply it by an arbitrary allowed channel vector. All other
endpoint responses vanish; the rank-one identity reads the plus contraction.
-/
theorem right_test (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : Lax342547.ProjectedPins.projected P i (e, false) ⊔ individualKeys W i e ≤ LinearMap.ker ψ)
    (c : H → Binary) (hc : c ∈ perpendicular (protectedChannel Q z (e, true))) :
    dotProduct (fullPlus F e i z
      (((x i).val e).mulVecLin (Lax342547.PrimalContractions.coordinates ψ))) c = 0 := by
  classical
  let E := barred W P (V e) (e, false)
  let ψnom := ψ.comp (Lax342547.ProjectedPins.primalProjection (H := H) i)
  have hψker : E ≤ LinearMap.ker ψnom := by
    intro v hv
    exact hψ (Lax342547.BarredSpaces.barred_projection W P (V e) (e, false) i ⟨v, hv, rfl⟩)
  let δG := (E.liftQ ψnom hψker).smulRight (⟨c, hc⟩ : perpendicular (protectedChannel Q z (e, true)))
  have hr (j : Fin 2) : restriction E (protectedChannel Q z (e, true)) δG j =
      if j = i then ψ.smulRight c else 0 := by
    apply LinearMap.ext
    intro v
    by_cases hj : j = i
    · subst j
      ext a
      simp [restriction, δG, ψnom, Lax342547.ProjectedPins.primalProjection, primalEmbedding]
    · have hp : Lax342547.ProjectedPins.primalProjection i (primalEmbedding (H := H) j v) = 0 := by
        ext a
        simp [Lax342547.ProjectedPins.primalProjection, primalEmbedding, Ne.symm hj]
      change ((ψ (Lax342547.ProjectedPins.primalProjection i (primalEmbedding j v))) • c) = _
      rw [hp, map_zero, zero_smul, if_neg hj]
      rfl
  have hh := Lax342547.DerivativeResponses.component_annihilation W P Q U V F z x h e 0 δG
  simp only [componentResponse, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    restriction_zero, DerivativeContractions.ambient_zero_left, add_zero] at hh
  change (∑ j, Lax342547.TensorContractions.ambient (fullPlus F e j z)
    (restriction E (protectedChannel Q z (e, true)) δG j) ((x j).val e)) = 0 at hh
  simp only [hr] at hh
  rw [Finset.sum_eq_single i] at hh
  · rw [if_pos rfl, Lax342547.DerivativeContractions.right_rank_one] at hh
    exact hh
  · intro j _ hji
    rw [if_neg hji, DerivativeContractions.ambient_zero_right, LinearMap.zero_apply]
  · simp

/--
---
conclusion: Lax342547.DerivativeResponses.plus_contraction_zero
---
Pure annihilation and sparse exclusion place the plus contraction
in the actual plus primal pin. The rank-one derivative test kills its
orthogonal channel pairings; the actual row injection flag forces zero.
-/
theorem plus_contraction_zero {R : ℕ} (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (hU : ∀ j, IsCompl (protectedChannel P j (e, true)) (U e j))
    (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (Lax342547.ResidualLabels.chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : (x i).val e = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : Lax342547.ProjectedPins.projected P i (e, false) ⊔ individualKeys W i e ≤ LinearMap.ker ψ) :
    ((x i).val e).mulVecLin (Lax342547.PrimalContractions.coordinates ψ) = 0 := by
  have hpure := Lax342547.PureObstructions.component_annihilation W P U V x
    (Lax342547.DerivativeResponses.pure_annihilation W P Q U V F z x h) e
  have hd := Lax342547.PrimalContractions.unselected_pin_contraction W P A hA hfresh (U e) (V e) e hU
    (Lax342547.PureObstructions.endpointComponent e x) hpure i L hL hdisjoint Z hM ψ hψ
  apply Lax342547.ChannelChanges.row_injection_zero T hT F hF e i z ⟨_, hd⟩
  intro c hc
  exact Lax342547.DerivativeResponses.right_test W P Q U V F z x h e i ψ hψ c hc

/--
---
conclusion: Lax342547.DerivativeResponses.left_test
---
Use the individual plus functional in a rank-one allowed plus change.
The other endpoint is zero, and the reciprocal rank-one identity reads
the transposed residual through the actual minus baseline map.
-/
theorem left_test (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : Lax342547.ProjectedPins.projected P i (e, true) ⊔ individualKeys W i e ≤ LinearMap.ker ψ)
    (c : H → Binary) (hc : c ∈ perpendicular (protectedChannel Q z (e, false))) :
    dotProduct (fullMinus F e i z
      (((x i).val e).transpose.mulVecLin (Lax342547.PrimalContractions.coordinates ψ))) c = 0 := by
  classical
  let E := barred W P (U e) (e, true)
  let ψnom := ψ.comp (Lax342547.ProjectedPins.primalProjection (H := H) i)
  have hψker : E ≤ LinearMap.ker ψnom := by
    intro v hv
    exact hψ (Lax342547.BarredSpaces.barred_projection W P (U e) (e, true) i ⟨v, hv, rfl⟩)
  let δF := (E.liftQ ψnom hψker).smulRight (⟨c, hc⟩ : perpendicular (protectedChannel Q z (e, false)))
  have hr (j : Fin 2) : restriction E (protectedChannel Q z (e, false)) δF j =
      if j = i then ψ.smulRight c else 0 := by
    apply LinearMap.ext
    intro v
    by_cases hj : j = i
    · subst j
      ext a
      simp [restriction, δF, ψnom, Lax342547.ProjectedPins.primalProjection, primalEmbedding]
    · have hp : Lax342547.ProjectedPins.primalProjection i (primalEmbedding (H := H) j v) = 0 := by
        ext a
        simp [Lax342547.ProjectedPins.primalProjection, primalEmbedding, Ne.symm hj]
      change ((ψ (Lax342547.ProjectedPins.primalProjection i (primalEmbedding j v))) • c) = _
      rw [hp, map_zero, zero_smul, if_neg hj]
      rfl
  have hh := Lax342547.DerivativeResponses.component_annihilation W P Q U V F z x h e δF 0
  simp only [componentResponse, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    restriction_zero, DerivativeContractions.ambient_zero_right, zero_add] at hh
  change (∑ j, Lax342547.TensorContractions.ambient
    (restriction E (protectedChannel Q z (e, false)) δF j) (fullMinus F e j z) ((x j).val e)) = 0 at hh
  simp only [hr] at hh
  rw [Finset.sum_eq_single i] at hh
  · rw [if_pos rfl, Lax342547.DerivativeContractions.left_rank_one, dotProduct_comm] at hh
    exact hh
  · intro j _ hji
    rw [if_neg hji, DerivativeContractions.ambient_zero_left, LinearMap.zero_apply]
  · simp

/--
---
conclusion: Lax342547.DerivativeResponses.minus_contraction_zero
---
Transpose the pure nominal tensor test and retain the minus protected
/private complement. Sparse exclusion puts the reciprocal contraction
in the actual minus primal pin; its derivative tests and the column
injection flag then force zero.
-/
theorem minus_contraction_zero {R : ℕ} (W : Lists k n b degree r hr)
    (P Q : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (A : Fin 2 → Finset (Fin b → Binary))
    (hA : Lax342547.PinLabelExclusions.Covers P A R)
    (hfresh : ∀ i z t, (W.left i z t).label ∉ A i)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (T : Lax342547.SmallTables.Table P Q) (hT : Lax342547.SmallTables.Injecting T)
    (F : CrossForms (Component (Tag k)) (Coordinate k n b degree) H) (hF : Extends F T) (z : Fin 2)
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P Q U V F z x)
    (e : Component (Tag k)) (i : Fin 2)
    (hV : ∀ j, IsCompl (protectedChannel P j (e, false)) (V e j))
    (L : Finset (Fin b → Binary)) (hL : L.card ≤ R)
    (hdisjoint : Disjoint L (Lax342547.ResidualLabels.chosenLabels W i))
    (Z : (Fin b → Binary) → Matrix (Option (Base k n)) (Option (Base k n)) Binary)
    (hM : (x i).val e = ∑ s ∈ L, Lax342547.TensorBlocks.block selectorEval s (Z s))
    (ψ : Module.Dual Binary (Vector k n b degree))
    (hψ : Lax342547.ProjectedPins.projected P i (e, true) ⊔ individualKeys W i e ≤ LinearMap.ker ψ) :
    ((x i).val e).transpose.mulVecLin (Lax342547.PrimalContractions.coordinates ψ) = 0 := by
  classical
  have hpure := Lax342547.PureObstructions.component_annihilation W P U V x
    (Lax342547.DerivativeResponses.pure_annihilation W P Q U V F z x h) e
  have ht := Lax342547.DerivativeContractions.paired_transpose _ _ _ hpure
  have hMt : ((x i).val e).transpose = ∑ s ∈ L,
      Lax342547.TensorBlocks.block selectorEval s ((Z s).transpose) := by
    rw [hM]
    ext a b
    simp [Matrix.sum_apply, Matrix.transpose_apply, Lax342547.TensorBlocks.block,
      mul_comm]
  have hd := Lax342547.PrimalContractions.unselected_pin_contraction_mode W P A hA hfresh false
    (V e) (U e) e hV
    (fun j => ((x j).val e).transpose) ht i L hL hdisjoint
    (fun s => (Z s).transpose) hMt ψ hψ
  apply Lax342547.ChannelChanges.column_injection_zero T hT F hF e i z ⟨_, hd⟩
  intro c hc
  exact Lax342547.DerivativeResponses.left_test W P Q U V F z x h e i ψ hψ c hc

end Lax342547Proofs.DerivativeResponses
