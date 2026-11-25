import Lax793645.ConstructionData

/-!
---
title: Duality for the four scalar equations
type: lemma
---
An insoluble scalar target has a linear functional that vanishes on every available
generator and is nonzero on the target. Surjectivity on the base coordinates forces at
least one of the four coupled weights to be nonzero.
-/

namespace Lax793645.ScalarDuality

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Submodule Finset Function Module
open scoped BigOperators
open Lax793645.ConstructionData.Binary.HadwigerCounterexample.StatusAnalysis
variable {d e : ℕ}
variable {A B : Rates}

axiom counter_score (V : StatusSp A B) (T : Cabinet A B)
    (h : ¬scorecard V T) :
    ∃ g : Critic A B,Counter g V ∧ ∑ i,g.alf i (T i)≠0

end

section
open Lax793645.ConstructionData.Binary
open Lax793645.ConstructionData.Frames
open Lax793645.ConstructionData.Binary.HadwigerCounterexample
open Matrix LinearMap Submodule Finset Function Module
open scoped BigOperators
open Lax793645.ConstructionData.Binary.HadwigerCounterexample.StatusAnalysis
variable {d e : ℕ}
variable {A B : Rates}

axiom critic_nz (V : StatusSp A B) (T : Cabinet A B) (hV : ∀ i,coverBase (V i)) (g : Critic A B)
    (h : Counter g V) (hh : ∑ i,g.alf i (T i)≠0) : g.altL≠0 ∨ g.altR≠0

end

end Lax793645.ScalarDuality
