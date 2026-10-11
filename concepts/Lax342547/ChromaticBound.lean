import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
---
title: The chromatic lower bound for independence number two
type: lemma
---
A finite graph of independence number at most two satisfies
$|V(G)|\le 2\chi(G)$, since every color class has at most two vertices.
-/

namespace Lax342547.ChromaticBound

axiom card_le_twice_chromaticNumber_of_indepNum
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hα : G.indepNum ≤ 2) :
    Fintype.card V ≤ 2 * G.chromaticNumber.toNat

end Lax342547.ChromaticBound
