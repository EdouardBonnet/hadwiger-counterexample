import Lax342547.KeyMeasures
import Lax342547.CellAveraging
import Lax342547.CollisionPruning

/-!
---
title: Key-indexed original record cells
type: lemma
---
Refining a key by a unary record preserves accepted key mass. Matching retained record cells sum to the retained collision mass, with nonnegative subprobability weights.
-/

namespace Lax342547.RecordCollision

open Lax342547.KeyMeasures Lax342547.CellAveraging Lax342547.RetainedImages Lax342547.CollisionPruning

noncomputable def keyRecordMass {Ω Q C : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (key : Ω → Q) (record : Ω → C) (accept : Ω → Prop) (q : Q) (c : C) : ℝ :=
  recordMass ρ (fun ω => (key ω,record ω)) accept (q,c)

axiom key_record_mass_total {Ω Q C : Type} [Fintype Ω] [Fintype C]
    (ρ : Ω → ℝ) (key : Ω → Q) (record : Ω → C) (accept : Ω → Prop) (q : Q) :
    (∑ c, keyRecordMass ρ key record accept q c) = keyMass ρ key accept q

axiom retained_key_record_identity {Q C D : Type} [Fintype Q] [Fintype C] [Fintype D]
    (a : Q → C → ℝ) (b : Q → D → ℝ) (τ : ℝ) :
    retainedPairs (fun qc : Q × C => a qc.1 qc.2) (fun qd : Q × D => b qd.1 qd.2)
      (fun qc qd => qc.1 = qd.1) τ = ∑ q, retained (a q) τ * retained (b q) τ

axiom key_record_mass_nonneg {Ω Q C : Type} [Fintype Ω]
    (ρ : Ω → ℝ) (key : Ω → Q) (record : Ω → C) (accept : Ω → Prop)
    (hρ : ∀ ω, 0 ≤ ρ ω) (q : Q) (c : C) : 0 ≤ keyRecordMass ρ key record accept q c

axiom key_record_mass_subprobability {Ω Q C : Type} [Fintype Ω] [Fintype Q] [Fintype C]
    (ρ : Ω → ℝ) (key : Ω → Q) (record : Ω → C) (accept : Ω → Prop)
    (hρ : ∀ ω, 0 ≤ ρ ω) (hsum : ∑ ω, ρ ω ≤ 1) :
    (∑ q, ∑ c, keyRecordMass ρ key record accept q c) ≤ 1

end Lax342547.RecordCollision
