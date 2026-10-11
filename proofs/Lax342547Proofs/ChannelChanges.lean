import Lax342547.ChannelChanges
import Lax342547.TableContractions
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Lax342547Proofs.TensorAnnihilators

namespace Lax342547Proofs.ChannelChanges

open Lax342547.MomentSpace Lax342547.TableSpaces Lax342547.PairedAnnihilators
open Lax342547.PrimalContractions Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.SmallTables Lax342547.TableContractions
open Lax342547.TensorAnnihilators

set_option backward.isDefEq.respectTransparency false

open Lax342547.ChannelChanges

/--
---
conclusion: Lax342547.ChannelChanges.frozen
---
The domain quotient kills a frozen input. An allowed value pairs to
zero with an opposite protected-channel projection.
-/
theorem frozen {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z : Fin 2)
    (v w : Nominal B H) (h : v ∈ D ∨ channelProjection z w ∈ S) :
    channelChange D S δ z v w = 0 := by
  change dotProduct (δ (D.mkQ v)).val (channelProjection z w) = 0
  rcases h with hv | hw
  · have hz : D.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz, map_zero]
    simp
  · rw [dotProduct_comm]
    have hp := (δ (D.mkQ v)).property
    change ∀ u ∈ S, dotProduct u (δ (D.mkQ v)).val = 0 at hp
    exact hp _ hw

/--
---
conclusion: Lax342547.ChannelChanges.opposite_primal
---
A primal embedding has zero channel projection, so every allowed
channel change is zero on that opposite primal argument.
-/
theorem opposite_primal {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z j : Fin 2)
    (v : Nominal B H) (w : B → Binary) :
    channelChange D S δ z v (primalEmbedding j w) = 0 := by
  apply Lax342547.ChannelChanges.frozen D S δ z v _
  right
  have hz : channelProjection z (primalEmbedding (H := H) j w) = 0 := by
    ext h
    simp [channelProjection, primalEmbedding]
  rw [hz]
  exact S.zero_mem

/--
---
conclusion: Lax342547.ChannelChanges.pin_frozen
---
Every actual pin channel projection lies in its protected channel,
which is killed by the allowed value space.
-/
theorem pin_frozen {Comp B H N : Type} [Fintype H]
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (D : Submodule Binary (Nominal B H)) (a : Comp × Bool) (z : Fin 2)
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular (protectedChannel P z a))
    (v w : Nominal B H) (hw : w ∈ P.space a) :
    channelChange D (protectedChannel P z a) δ z v w = 0 :=
  Lax342547.ChannelChanges.frozen D _ δ z v w (Or.inr (Submodule.mem_map.mpr ⟨w, hw, rfl⟩))

/--
---
conclusion: Lax342547.ChannelChanges.perpendicular_detects
---
Coordinate duality identifies every functional annihilating the
protected space with a perpendicular channel vector. Double annihilation
therefore detects membership in the protected space.
-/
theorem perpendicular_detects {H : Type} [Fintype H]
    (S : Submodule Binary (H → Binary)) (v : H → Binary)
    (h : ∀ c ∈ perpendicular S, dotProduct v c = 0) : v ∈ S := by
  classical
  rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := S)]
  apply (Submodule.mem_dualCoannihilator _).mpr
  intro φ hφ
  have hc : coordinates φ ∈ perpendicular S := by
    change ∀ w ∈ S, dotProduct w (coordinates φ) = 0
    intro w hw
    change (∑ a, w a * dualCoordinates φ a) = 0
    rw [← Lax342547Proofs.TensorAnnihilators.functional_coordinates φ w]
    exact (Submodule.mem_dualAnnihilator φ).mp hφ w hw
  have hz := h (coordinates φ) hc
  change (∑ a, v a * dualCoordinates φ a) = 0 at hz
  rw [← Lax342547Proofs.TensorAnnihilators.functional_coordinates φ v] at hz
  exact hz

/--
---
conclusion: Lax342547.ChannelChanges.row_injection_zero
---
The full cross form agrees with the actual row table on pinned inputs.
Orthogonal tests put its channel value in the same-sign protected space;
the first table injection flag forces the pinned vector to zero.
-/
theorem row_injection_zero {Comp B H N : Type} [Fintype H]
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (hT : Injecting T) (F : CrossForms Comp B H) (hF : Extends F T)
    (e : Comp) (i z : Fin 2) (d : pinnedPrimal P i (e, true))
    (h : ∀ c ∈ perpendicular (protectedChannel Q z (e, true)),
      dotProduct (fullPlus F e i z d.val) c = 0) : d.val = 0 := by
  classical
  have he : fullPlus F e i z d.val =
      rowChannels P Q (e, true) (e, false) (T.forward e) i z d := by
    ext a
    exact hF.1 e (tablePinnedPrimal P (e, true) i d)
      (tableChannel Q (e, false) z (Pi.single a 1))
  have hmem := Lax342547.ChannelChanges.perpendicular_detects (protectedChannel Q z (e, true)) _ h
  rw [he] at hmem
  have hz : (protectedChannel Q z (e, true)).mkQ
      (rowChannels P Q (e, true) (e, false) (T.forward e) i z d) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hmem
  have hd : d = 0 := (hT e i z).1 (by simpa using hz)
  exact congrArg Subtype.val hd

/--
---
conclusion: Lax342547.ChannelChanges.column_injection_zero
---
The reciprocal cross form agrees with the actual column table on
pinned inputs. Orthogonal tests kill its protected-channel quotient,
and the second actual injection flag forces the vector to zero.
-/
theorem column_injection_zero {Comp B H N : Type} [Fintype H]
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (hT : Injecting T) (F : CrossForms Comp B H) (hF : Extends F T)
    (e : Comp) (i z : Fin 2) (d : pinnedPrimal P i (e, false))
    (h : ∀ c ∈ perpendicular (protectedChannel Q z (e, false)),
      dotProduct (fullMinus F e i z d.val) c = 0) : d.val = 0 := by
  classical
  have he : fullMinus F e i z d.val =
      columnChannels Q P (e, true) (e, false) (T.reverse e) z i d := by
    ext a
    exact hF.2 e (tableChannel Q (e, true) z (Pi.single a 1))
      (tablePinnedPrimal P (e, false) i d)
  have hmem := Lax342547.ChannelChanges.perpendicular_detects (protectedChannel Q z (e, false)) _ h
  rw [he] at hmem
  have hz : (protectedChannel Q z (e, false)).mkQ
      (columnChannels Q P (e, true) (e, false) (T.reverse e) z i d) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hmem
  have hd : d = 0 := (hT e i z).2.1 (by simpa using hz)
  exact congrArg Subtype.val hd

/--
---
conclusion: Lax342547.ChannelChanges.channel_entry
---
Evaluation on an opposite channel basis vector reads precisely the
corresponding coordinate of the allowed quotient-map output.
-/
theorem channel_entry {B H : Type} [Fintype H]
    (D : Submodule Binary (Nominal B H)) (S : Submodule Binary (H → Binary))
    (δ : (Nominal B H ⧸ D) →ₗ[Binary] perpendicular S) (z : Fin 2)
    (v : Nominal B H) (h : H) : by
      classical
      exact channelChange D S δ z v (channelEmbedding z (Pi.single h 1)) =
        (δ (D.mkQ v)).val h := by
  classical
  have hc : channelProjection z (channelEmbedding (B := B) z (Pi.single h 1)) = Pi.single h 1 := by
    ext a
    simp [channelProjection, channelEmbedding]
  change dotProduct (δ (D.mkQ v)).val (channelProjection z (channelEmbedding z (Pi.single h 1))) = _
  rw [hc]
  simp

end Lax342547Proofs.ChannelChanges
