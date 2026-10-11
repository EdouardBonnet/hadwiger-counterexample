import Lax342547.ModeBudgets

/-!
---
title: Join-stable classes of mode covers
type: lemma
---
Finite exposed spans remain in any class of mode spaces containing zero and closed under joins, including componentwise classes.
-/

namespace Lax342547.CoverClasses



def JoinClosed {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (P : Submodule K V → Prop) : Prop :=
    P ⊥ ∧ ∀ S T, P S → P T → P (S ⊔ T)

axiom finite_join_closed {K V ι : Type} [Field K] [DecidableEq ι]
    [AddCommGroup V] [Module K V] (P : Submodule K V → Prop) (hP : JoinClosed P)
    (S : ι → Submodule K V) (I : Finset ι) (hS : ∀ i ∈ I, P (S i)) : P (I.sup S)

end Lax342547.CoverClasses
