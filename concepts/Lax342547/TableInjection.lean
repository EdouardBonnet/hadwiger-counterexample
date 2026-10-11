import Lax342547.RawContractions
import Lax342547.FiniteInjection

/-!
---
title: Actual table injection and ambient pin failures
type: lemma
---
Restrict the actual cross Gram forms to the numerical table spaces. Each
of the sixteen component tests is precisely an ambient primal-image
injection modulo the opposite unit's same-sign protected channels.
-/

namespace Lax342547.TableInjection

open Lax342547.MomentSpace Lax342547.RawFrames Lax342547.ExactPins
open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableContractions
open Lax342547.RawContractions Lax342547.FiniteInjection

variable {Comp B H N : Type} [Fintype B] [Fintype H] [Fintype N]
  {E : Matrix B B Binary}

def rawTable (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) : Table P Q where
  forward e := ((rawForms A Bmap).forward e).compl₁₂
    (tableSpace P (e, true)).subtype (tableSpace Q (e, false)).subtype
  reverse e := ((rawForms A Bmap).reverse e).compl₁₂
    (tableSpace Q (e, true)).subtype (tableSpace P (e, false)).subtype

def primalMatrix (A : Fin 2 → Comp → Frame B H N E) (e : Comp) (i : Fin 2)
    (s : Bool) : Matrix N B Binary := if s then (A i e).P else (A i e).Q

def oppositeChannel (A : Fin 2 → Comp → Frame B H N E) (e : Comp) (i : Fin 2)
    (s : Bool) : Matrix N H Binary := if s then (A i e).Y else (A i e).X

def primalImage (P : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A : Fin 2 → Comp → Frame B H N E) (e : Comp) (i : Fin 2) (s : Bool) :
    Submodule Binary (N → Binary) :=
  (pinnedPrimal P i (e, s)).map (primalMatrix A e i s).mulVecLin

def Failed (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) (e : Comp) (i z : Fin 2)
    (s role : Bool) : Prop :=
  if role then
    pinFailure (primalImage Q Bmap e i s) (oppositeChannel A e z s)
      (protectedChannel P z (e, s))
  else
    pinFailure (primalImage P A e i s) (oppositeChannel Bmap e z s)
      (protectedChannel Q z (e, s))

axiom actual_table_injecting_iff (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) :
    Injecting (rawTable P Q A Bmap) ↔ ∀ e i z s role,¬ Failed P Q A Bmap e i z s role

axiom admissible_injection_iff (P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N)
    (A Bmap : Fin 2 → Comp → Frame B H N E) (T : Table P Q)
    (hT : Admissible T Lax342547.ReferencePins.observation Lax342547.ReferencePins.observation A Bmap) :
    Injecting T ↔ Injecting (rawTable P Q A Bmap)

end Lax342547.TableInjection
