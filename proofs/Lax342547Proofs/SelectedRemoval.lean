import Lax342547.SelectedRemoval
import Lax342547Proofs.SelectedScalars
import Lax342547Proofs.FrozenValues
import Lax342547Proofs.Atoms
import Lax342547Proofs.UnaryMixer

namespace Lax342547Proofs.SelectedRemoval

open Lax342547.MomentSpace Lax342547.TagGeometry Lax342547.ConcreteGeometry
open Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.PairedWitnesses
open Lax342547.ExactPins Lax342547.PureObstructions Lax342547.SelectedRemoval
open Lax342547.PairedAnnihilators Lax342547.BarredSpaces Lax342547.TableSpaces

set_option backward.isDefEq.respectTransparency false

variable {k n b degree r : ℕ} {hr : 2 * r ≤ n} {H N : Type}

theorem pureResponse_single {B H : Type} [Fintype B]
    (D E : Submodule Binary (Nominal B H))
    (β : (Nominal B H ⧸ D) →ₗ[Binary] (Nominal B H ⧸ E) →ₗ[Binary] Binary)
    (i : Fin 2) (M : Matrix B B Binary) : by
  classical
  exact pureResponse D E β (Pi.single i M) =
    matrixPair (LinearMap.BilinForm.toMatrix'
      (β.compl₁₂ (D.mkQ.comp (primalEmbedding i)) (E.mkQ.comp (primalEmbedding i)))) M := by
  classical
  simp only [pureResponse, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

/--
---
conclusion: Lax342547.SelectedRemoval.atom_annihilates
---
In incident components the selected atom contracts to a bilinear test
of its two nominal key vectors. Both are zero in the barred quotients.
All other components of the atom are zero.
-/
theorem atom_annihilates (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (i : Fin 2) (u : Σ z, Fin (W.length i z)) :
    Annihilates W P U V (Pi.single i (W.left i u.1 u.2).profile) := by
  classical
  intro β
  simp only [response, LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_eq_zero
  intro e _
  have he : endpointComponent e (Pi.single i (W.left i u.1 u.2).profile) =
      Pi.single i ((W.left i u.1 u.2).profile.val e) := by
    ext j
    by_cases hji : j = i <;> simp [endpointComponent, hji]
  rw [he, pureResponse_single]
  by_cases htag : (W.left i u.1 u.2).tag ∈ e.val
  · simp only [Lax342547.WitnessAtoms.PointAtom.profile, Atoms.atom_component, htag, if_pos]
    change matrixPair (LinearMap.BilinForm.toMatrix' _)
      (Matrix.vecMulVec (W.left i u.1 u.2).vector (W.left i u.1 u.2).vector) = 0
    rw [UnaryMixer.matrixPair_vecMulVec, Matrix.toBilin'_toMatrix']
    change β e ((barred W P (U e) (e, true)).mkQ
        (primalEmbedding i (W.left i u.1 u.2).vector))
      ((barred W P (V e) (e, false)).mkQ
        (primalEmbedding i (W.left i u.1 u.2).vector)) = 0
    have hkey := FrozenValues.key_mem (H := H) W e i u.1 u.2 htag
    have hmem : primalEmbedding (H := H) i (W.left i u.1 u.2).vector ∈
        barred W P (U e) (e, true) :=
      (show Lax342547.PairedKeys.keys W e ≤ barred W P (U e) (e, true) from
        le_trans le_sup_right le_sup_left) hkey
    have hz : (barred W P (U e) (e, true)).mkQ
        (primalEmbedding i (W.left i u.1 u.2).vector) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [hz]
    simp
  · simp [Lax342547.WitnessAtoms.PointAtom.profile, Atoms.atom_component, htag]

/--
---
conclusion: Lax342547.SelectedRemoval.selected_part_annihilates
---
Expand the endpoint tuple into coordinate singletons, then use linearity
and the selected-atom test on every term of the finite sums.
-/
theorem selected_part_annihilates (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) :
    Annihilates W P U V (selectedPart W c) := by
  classical
  intro β
  rw [← Finset.univ_sum_single (selectedPart W c), map_sum]
  apply Finset.sum_eq_zero
  intro i _
  change response W P U V β ((LinearMap.single Binary (fun _ : Fin 2 => Profile k n b degree) i)
    (∑ u, c i u • (W.left i u.1 u.2).profile)) = 0
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro u _
  change c i u • response W P U V β (Pi.single i (W.left i u.1 u.2).profile) = 0
  rw [atom_annihilates W P U V i u β, smul_zero]

/--
---
conclusion: Lax342547.SelectedRemoval.subtract_annihilates
---
Each response is linear, so subtracting the selected part preserves
its zero value on the original pure obstruction.
-/
theorem subtract_annihilates (W : Lists k n b degree r hr)
    (P : Pin (Component (Tag k) × Bool) (Fin 2 × (Coordinate k n b degree ⊕ H)) N)
    (U V : Component (Tag k) → Fin 2 → Submodule Binary (H → Binary))
    (x : Fin 2 → Profile k n b degree) (h : Annihilates W P U V x)
    (c : ∀ i : Fin 2, (Σ z, Fin (W.length i z)) → Binary) :
    Annihilates W P U V (x - selectedPart W c) := by
  intro β
  rw [map_sub, h β, selected_part_annihilates W P U V c β, sub_self]

end Lax342547Proofs.SelectedRemoval
