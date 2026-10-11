import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic

/-!
---
title: Finite ordered fingerprint budgets
type: definition and theorem
---
Padding a fingerprint with absent entries injects all fingerprints of length at most L into words of length L over the raw alphabet with one extra symbol. Thus their number is at most (card U + 1)^L.
-/

namespace Lax342547.FingerprintCounts



noncomputable def pad {U : Type} (L : ℕ) (l : List U) : List (Option U) :=
  l.map some ++ List.replicate (L-l.length) none

axiom pad_recovers {U : Type} (L : ℕ) (l : List U) : (pad L l).filterMap id = l

axiom pad_injective {U : Type} (L : ℕ) : Function.Injective (pad (U := U) L)

axiom pad_length {U : Type} (L : ℕ) (l : List U) (hl : l.length ≤ L) : (pad L l).length = L

axiom bounded_list_count {U : Type} [Fintype U] (T : Finset (List U)) (L : ℕ)
    (hL : ∀ l ∈ T, l.length ≤ L) : T.card ≤ (Fintype.card U+1)^L

end Lax342547.FingerprintCounts
