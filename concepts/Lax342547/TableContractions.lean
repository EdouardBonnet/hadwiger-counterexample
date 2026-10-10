import Lax342547.SmallTables
import Lax342547.TensorContractions

/-!
---
title: Table contractions on effective profiles and their full extensions
type: definition and theorem
---
The starred contraction is a linear functional on the actual effective
cut profiles. It uses both cross orientations of the table. Every full
nominal cross form extending the whole table has that same contraction
on effective profiles; admissibility alone is not asserted to suffice.
-/

namespace Lax342547.TableContractions

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.TableSpaces Lax342547.SmallTables

structure CrossForms (Comp B H : Type) where
  forward : Comp → LinearMap.BilinForm Binary ((Fin 2 × (B ⊕ H)) → Binary)
  reverse : Comp → LinearMap.BilinForm Binary ((Fin 2 × (B ⊕ H)) → Binary)

def CrossForms.flip {Comp B H : Type} (F : CrossForms Comp B H) : CrossForms Comp B H :=
  ⟨F.reverse, F.forward⟩

def flipTable {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) : Table Q P := ⟨T.reverse, T.forward⟩

def Extends {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (F : CrossForms Comp B H) (T : Table P Q) : Prop :=
  (∀ e (v : tableSpace P (e, true)) (w : tableSpace Q (e, false)),
    F.forward e v.val w.val = T.forward e v w) ∧
  (∀ e (v : tableSpace Q (e, true)) (w : tableSpace P (e, false)),
    F.reverse e v.val w.val = T.reverse e v w)

def primalToTable {Comp B H N : Type}
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (a : Comp × Bool) (i : Fin 2) :
    projected P i a →ₗ[Binary] tableSpace P a where
  toFun v := ⟨primalEmbedding i v.val, by
    intro j
    by_cases hji : j = i
    · subst j
      simp [primalProjection, primalEmbedding]
    · have hz : primalProjection j (primalEmbedding (H := H) i v.val) = 0 := by
        ext b
        simp [primalProjection, primalEmbedding, hji]
      rw [hz]
      exact (projected P j a).zero_mem⟩
  map_add' v w := Subtype.ext ((primalEmbedding i).map_add v.val w.val)
  map_smul' c v := Subtype.ext ((primalEmbedding i).map_smul c v.val)

noncomputable def plus {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (e : Comp) (i z : Fin 2) : projected P i (e, true) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => T.forward e (primalToTable P (e, true) i v)
        (tableChannel Q (e, false) z (Pi.single h 1))
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

noncomputable def minus {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (e : Comp) (i z : Fin 2) : projected P i (e, false) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => T.reverse e (tableChannel Q (e, true) z (Pi.single h 1))
        (primalToTable P (e, false) i v)
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

noncomputable def fullPlus {Comp B H : Type} (F : CrossForms Comp B H) (e : Comp) (i z : Fin 2) :
    (B → Binary) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => F.forward e (primalEmbedding i v) (channelEmbedding z (Pi.single h 1))
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

noncomputable def fullMinus {Comp B H : Type} (F : CrossForms Comp B H) (e : Comp) (i z : Fin 2) :
    (B → Binary) →ₗ[Binary] (H → Binary) := by
  classical
  exact
    { toFun := fun v h => F.reverse e (channelEmbedding z (Pi.single h 1)) (primalEmbedding i v)
      map_add' := by intro v w; ext h; simp
      map_smul' := by intro c v; ext h; simp }

def component {Comp B H N : Type} (X : Submodule Binary (Comp → Matrix B B Binary))
    (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N) (i : Fin 2) (e : Comp) :
    effective X P i →ₗ[Binary] tensorSpace (projected P i (e, true)) (projected P i (e, false)) where
  toFun x := ⟨x.val.val e, x.property e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def starContraction {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) :
    effective X P i →ₗ[Binary] Binary :=
  ∑ e, (TensorContractions.contraction (plus T e i z) (minus T e i z)).comp (component X P i e)

noncomputable def fullContraction {Comp B H : Type} [Fintype Comp] [Fintype B] [Fintype H]
    (F : CrossForms Comp B H) (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) :
    X →ₗ[Binary] Binary :=
  ∑ e, (TensorContractions.ambient (fullPlus F e i z) (fullMinus F e i z)).comp
    ((LinearMap.proj e).comp X.subtype)

axiom star_extension {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (F : CrossForms Comp B H) (hF : Extends F T)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) (x : effective X P i) :
    starContraction T X i z x = fullContraction F X i z x.val

end Lax342547.TableContractions
