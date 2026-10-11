import Lax342547.SmallTables

namespace Lax342547Proofs.SmallTables

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.TableSpaces Lax342547.SmallTables

variable {Comp B H N : Type} [Fintype N] {ΩA ΩB : Type}

/--
---
conclusion: Lax342547.SmallTables.admissible_iff_filters
---
On each leaf a pinned input has its stored image. Substituting that image
in each cross orientation leaves a condition on the other unit alone.
If both inputs are pinned, the two substitutions give the same numerical
test, so no additional joint orientation filter is necessary.
-/
theorem admissible_iff_filters {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (A : ΩA → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary))
    (Bmap : ΩB → (Comp × Bool) → ((Fin 2 × (B ⊕ H)) → Binary) →ₗ[Binary] (N → Binary))
    (oA : ΩA) (oB : ΩB) (hA : oA ∈ P.event A) (hB : oB ∈ Q.event Bmap) :
    Admissible T A Bmap oA oB ↔ oA ∈ leftFilter T A ∧ oB ∈ rightFilter T Bmap := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro e v w hw
      simpa only [hB (e, false) ⟨w.val, hw⟩] using h.1 e v w (Or.inr hw)
    · intro e v w hv
      simpa only [hB (e, true) ⟨v.val, hv⟩] using h.2 e v w (Or.inl hv)
    · intro e v w hv
      simpa only [hA (e, true) ⟨v.val, hv⟩] using h.1 e v w (Or.inl hv)
    · intro e v w hw
      simpa only [hA (e, false) ⟨w.val, hw⟩] using h.2 e v w (Or.inr hw)
  · rintro ⟨hL, hR⟩
    constructor
    · intro e v w hp
      rcases hp with hv | hw
      · simpa only [hA (e, true) ⟨v.val, hv⟩] using hR.1 e v w hv
      · simpa only [hB (e, false) ⟨w.val, hw⟩] using hL.1 e v w hw
    · intro e v w hp
      rcases hp with hv | hw
      · simpa only [hB (e, true) ⟨v.val, hv⟩] using hL.2 e v w hv
      · simpa only [hA (e, false) ⟨w.val, hw⟩] using hR.2 e v w hw

/--
---
conclusion: Lax342547.SmallTables.raw_admissible_iff_filters
---
Use the actual joint plus/minus frame observations at both endpoints.
Their exact-pin events give the fixed images required by the separation
theorem, with no independence assumption on the endpoints of a unit.
-/
theorem raw_admissible_iff_filters [Fintype B] [Fintype H] {E : Matrix B B Binary}
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (oA oB : Fin 2 → Comp → Lax342547.RawFrames.Frame B H N E)
    (hA : oA ∈ P.event Lax342547.ReferencePins.observation)
    (hB : oB ∈ Q.event Lax342547.ReferencePins.observation) :
    Admissible T Lax342547.ReferencePins.observation Lax342547.ReferencePins.observation oA oB ↔
      oA ∈ leftFilter T Lax342547.ReferencePins.observation ∧
      oB ∈ rightFilter T Lax342547.ReferencePins.observation :=
  Lax342547.SmallTables.admissible_iff_filters T _ _ oA oB hA hB

end Lax342547Proofs.SmallTables
