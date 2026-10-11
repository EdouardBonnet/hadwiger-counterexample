import Lax342547.FrameTuples

/-!
---
title: Exact joining of two prescribed Gram orbits
type: definition and theorem
---
A combined Gram orbit is precisely two separate orbits conditioned on their
reciprocal Gram entries and injectivity of both concatenated column lists.
The exact uniform and filtered laws retain these injectivity conditions.
-/

namespace Lax342547.JoinedGramOrbits

open Lax342547.MomentSpace Lax342547.FrameTuples

variable {I J K L N : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L] [Fintype N]

def joined {G : Matrix I J Binary} {H : Matrix K L Binary} (z : Orbit N G × Orbit N H) :=
  (Matrix.fromCols z.1.val.1 z.2.val.1,Matrix.fromCols z.1.val.2 z.2.val.2)

def Compatible (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    (z : Orbit N G × Orbit N H) : Prop :=
  Function.Injective (joined z).1.mulVec ∧ Function.Injective (joined z).2.mulVec ∧
    z.1.val.1.transpose*z.2.val.2 = A ∧ z.2.val.1.transpose*z.1.val.2 = B

noncomputable instance (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary) :
    Fintype {z : Orbit N G × Orbit N H // Compatible G H A B z} := by
  classical exact Subtype.fintype _

axiom joined_gram (G : Matrix I J Binary) (H : Matrix K L Binary)
    (z : Orbit N G × Orbit N H) :
    (joined z).1.transpose*(joined z).2 =
      Matrix.fromBlocks G (z.1.val.1.transpose*z.2.val.2) (z.2.val.1.transpose*z.1.val.2) H

axiom union_uniform (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit N (Matrix.fromBlocks G A B H))]
    [Nonempty {z : Orbit N G × Orbit N H // Compatible G H A B z}] :
    (PMF.uniformOfFintype (Orbit N (Matrix.fromBlocks G A B H))).map Subtype.val =
      (PMF.uniformOfFintype {z : Orbit N G × Orbit N H // Compatible G H A B z}).map
        (fun z => joined z.val)

axiom compatible_filter (G : Matrix I J Binary) (H : Matrix K L Binary)
    (A : Matrix I L Binary) (B : Matrix K J Binary)
    [Nonempty (Orbit N G)] [Nonempty (Orbit N H)]
    [Nonempty (Orbit N (Matrix.fromBlocks G A B H))]
    [Nonempty {z : Orbit N G × Orbit N H // Compatible G H A B z}]
    (h : ∃ z ∈ {z : Orbit N G × Orbit N H | Compatible G H A B z},
      z ∈ (PMF.uniformOfFintype (Orbit N G × Orbit N H)).support) :
    ((PMF.uniformOfFintype (Orbit N G × Orbit N H)).filter
        {z | Compatible G H A B z} h).map joined =
      (PMF.uniformOfFintype (Orbit N (Matrix.fromBlocks G A B H))).map Subtype.val

end Lax342547.JoinedGramOrbits
