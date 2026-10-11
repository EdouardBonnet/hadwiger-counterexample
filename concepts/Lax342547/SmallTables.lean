import Lax342547.TableSpaces
import Lax342547.ReferencePins

/-!
---
title: Numerical cross tables, injection flags, and unary admissibility
type: lemma
---
A table records both cross orientations on the actual projected table
spaces. Its injection quotients use the protected channel of the same
sign as the pinned primal input, as in Definition 6.1. Admissibility on
exact-pin events separates into two filters on individual orientations.
-/

namespace Lax342547.SmallTables

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins Lax342547.TableSpaces

variable {Comp B H N : Type}

structure Table (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) where
  forward : ∀ e, tableSpace P (e, true) →ₗ[Binary] tableSpace Q (e, false) →ₗ[Binary] Binary
  reverse : ∀ e, tableSpace Q (e, true) →ₗ[Binary] tableSpace P (e, false) →ₗ[Binary] Binary

def tableChannel (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) (i : Fin 2) :
    (H → Binary) →ₗ[Binary] tableSpace P a where
  toFun v := ⟨channelEmbedding i v, by
    intro j
    have hz : primalProjection j (channelEmbedding (B := B) i v) = 0 := by
      ext b
      simp [primalProjection, channelEmbedding]
    rw [hz]
    exact (projected P j a).zero_mem⟩
  map_add' v w := Subtype.ext ((channelEmbedding i).map_add v w)
  map_smul' c v := Subtype.ext ((channelEmbedding i).map_smul c v)

def tablePinnedPrimal (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a : Comp × Bool) (i : Fin 2) : pinnedPrimal P i a →ₗ[Binary] tableSpace P a where
  toFun v := ⟨primalEmbedding i v.val, fun _j => ⟨primalEmbedding i v.val, v.property, rfl⟩⟩
  map_add' v w := Subtype.ext ((primalEmbedding i).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((primalEmbedding i).map_smul c v.val)

noncomputable def rowChannels (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a b : Comp × Bool)
    (T : tableSpace P a →ₗ[Binary] tableSpace Q b →ₗ[Binary] Binary) (i z : Fin 2) :
    pinnedPrimal P i a →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun d h => T (tablePinnedPrimal P a i d) (tableChannel Q b z (Pi.single h 1))
      map_add' := by intro d d'; ext h; simp
      map_smul' := by intro c d; ext h; simp }

noncomputable def columnChannels (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (a b : Comp × Bool)
    (T : tableSpace P a →ₗ[Binary] tableSpace Q b →ₗ[Binary] Binary) (z i : Fin 2) :
    pinnedPrimal Q i b →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun d h => T (tableChannel P a z (Pi.single h 1)) (tablePinnedPrimal Q b i d)
      map_add' := by intro d d'; ext h; simp
      map_smul' := by intro c d; ext h; simp }

def Injecting {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q) : Prop :=
  ∀ e i z,
    Function.Injective (((protectedChannel Q z (e, true)).mkQ).comp
      (rowChannels P Q (e, true) (e, false) (T.forward e) i z)) ∧
    Function.Injective (((protectedChannel Q z (e, false)).mkQ).comp
      (columnChannels Q P (e, true) (e, false) (T.reverse e) z i)) ∧
    Function.Injective (((protectedChannel P z (e, true)).mkQ).comp
      (rowChannels Q P (e, true) (e, false) (T.reverse e) i z)) ∧
    Function.Injective (((protectedChannel P z (e, false)).mkQ).comp
      (columnChannels P Q (e, true) (e, false) (T.forward e) z i))

variable [Fintype N] {ΩA ΩB : Type}

def Admissible {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (A : ΩA → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary))
    (Bmap : ΩB → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary))
    (oA : ΩA) (oB : ΩB) : Prop :=
  (∀ e (v : tableSpace P (e, true)) (w : tableSpace Q (e, false)),
    v.val ∈ P.space (e, true) ∨ w.val ∈ Q.space (e, false) →
    T.forward e v w = dotProduct (A oA (e, true) v.val) (Bmap oB (e, false) w.val)) ∧
  (∀ e (v : tableSpace Q (e, true)) (w : tableSpace P (e, false)),
    v.val ∈ Q.space (e, true) ∨ w.val ∈ P.space (e, false) →
    T.reverse e v w = dotProduct (Bmap oB (e, true) v.val) (A oA (e, false) w.val))

def leftFilter {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (A : ΩA → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary)) : Set ΩA :=
  {oA | (∀ e (v : tableSpace P (e, true)) (w : tableSpace Q (e, false))
      (hw : w.val ∈ Q.space (e, false)),
      T.forward e v w = dotProduct (A oA (e, true) v.val) (Q.value (e, false) ⟨w.val, hw⟩)) ∧
    (∀ e (v : tableSpace Q (e, true)) (w : tableSpace P (e, false))
      (hv : v.val ∈ Q.space (e, true)),
      T.reverse e v w = dotProduct (Q.value (e, true) ⟨v.val, hv⟩) (A oA (e, false) w.val))}

def rightFilter {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (Bmap : ΩB → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary)) : Set ΩB :=
  {oB | (∀ e (v : tableSpace P (e, true)) (w : tableSpace Q (e, false))
      (hv : v.val ∈ P.space (e, true)),
      T.forward e v w = dotProduct (P.value (e, true) ⟨v.val, hv⟩) (Bmap oB (e, false) w.val)) ∧
    (∀ e (v : tableSpace Q (e, true)) (w : tableSpace P (e, false))
      (hw : w.val ∈ P.space (e, false)),
      T.reverse e v w = dotProduct (Bmap oB (e, true) v.val) (P.value (e, false) ⟨w.val, hw⟩))}

axiom admissible_iff_filters {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (A : ΩA → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary))
    (Bmap : ΩB → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary))
    (oA : ΩA) (oB : ΩB) (hA : oA ∈ P.event A) (hB : oB ∈ Q.event Bmap) :
    Admissible T A Bmap oA oB ↔ oA ∈ leftFilter T A ∧ oB ∈ rightFilter T Bmap

axiom raw_admissible_iff_filters [Fintype B] [Fintype H] {E : Matrix B B Binary}
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (oA oB : Fin 2 → Comp → Lax342547.RawFrames.Frame B H N E)
    (hA : oA ∈ P.event Lax342547.ReferencePins.observation)
    (hB : oB ∈ Q.event Lax342547.ReferencePins.observation) :
    Admissible T Lax342547.ReferencePins.observation Lax342547.ReferencePins.observation oA oB ↔
      oA ∈ leftFilter T Lax342547.ReferencePins.observation ∧
      oB ∈ rightFilter T Lax342547.ReferencePins.observation

end Lax342547.SmallTables
