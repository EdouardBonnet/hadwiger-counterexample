import Lax342547.SymmetricFactorization
import Lax342547.ConcreteCut

/-!
---
title: Counting tuples of symmetric matrices with bounded total rank
type: theorem
---
Separate the component rank tuple from the symmetric factorizations.
There are at most (K+1)^|E| rank tuples, and each permitted tuple uses
at most dK+K² binary entries. This is the finite profile count underlying
the low-rank profile bound in Lemma 5.5, before substituting the concrete
coordinate dimension.
-/

namespace Lax342547.ProfileCounting

open Lax342547.MomentSpace

axiom card_symmetric_profiles {I E : Type} [Fintype I] [Fintype E] (K : ℕ) :
    Nat.card {x : E → Matrix I I Binary //
      (∀ e, (x e).transpose = x e) ∧ ∑ e, (x e).rank ≤ K} ≤
      (K + 1) ^ Fintype.card E * 2 ^ (Fintype.card I * K + K * K)

open Lax342547.ConcreteGeometry Lax342547.ConcreteCut Lax342547.CutProfiles Lax342547.TagGeometry

axiom card_concrete_profiles (k n b degree K : ℕ) :
    Nat.card {x : Profile k n b degree // ∑ e, (x.val e).rank ≤ K} ≤
      (K + 1) ^ Fintype.card (Component (Tag k)) *
        2 ^ (Fintype.card (Coordinate k n b degree) * K + K * K)

end Lax342547.ProfileCounting
