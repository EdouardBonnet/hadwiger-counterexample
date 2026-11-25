import Lax793645.ConstructionData

/-!
---
title: Seven generators with independent labels
type: lemma
---
If the base projection is onto and its kernel has dimension at most 2, a target in the
edge span has a representation by 1 to 7 generators under the stated fresh-label
hypotheses. One lift gives the base value and two short corrections suffice in the
kernel.
-/

namespace Lax793645.FreshWitnessLists

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
open Lax793645.ConstructionData.Frames.IndependentClub
axiom seven_list
    {L I S X Y : Type} [DecidableEq L] [DecidableEq I] [Fintype S]
    [AddCommGroup X] [Module F X] [Module.Finite F X]
    [AddCommGroup Y] [Module F Y] (C : Club I X L) (U : Bool → Space (Vec S)) (v : Bool → I → Vec S)
    (s : Straps L) (π : X →ₗ[F] Y) (V : Space X)
    (hspan : ∀ p : Finset I,p.card ≤ 4 →
      ration C (enlarge U v p) v s π=V ⊓ LinearMap.ker π)
    (hdim : dim (V ⊓ LinearMap.ker π : Space X) ≤ 2)
    (hchoose : ∀ y,∃ i,C.zone s i ∧ C.writes i∈V ∧ π (C.writes i)=y ∧
      ∀ b,(U b).mkQ (v b i) ≠ 0)
    (x : X) (hx : x∈V) :
    ∃ p : Finset I,bundle C U v p s ∧ C.contents p=x ∧ 1 ≤ p.card ∧ p.card ≤ 7

end

end Lax793645.FreshWitnessLists
