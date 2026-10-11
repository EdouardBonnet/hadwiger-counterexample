import Lax342547.LeafImages

/-!
---
title: Append fresh directions to the independent key tuple
type: lemma
---
Key directions independent modulo old pins and additional directions independent modulo pins plus keys form a joint tuple independent modulo old pins. Its full rank is available to the leaf image cap.
-/

namespace Lax342547.JointDirections

open Lax342547.MomentSpace

axiom appended_quotient_injective {U V W : Type}
    [AddCommGroup U] [Module Binary U] [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W]
    (P : Submodule Binary W) (keys : U →ₗ[Binary] W) (fresh : V →ₗ[Binary] W)
    (hkeys : Function.Injective (P.mkQ.comp keys))
    (hfresh : Function.Injective ((P ⊔ LinearMap.range keys).mkQ.comp fresh)) :
    Function.Injective (P.mkQ.comp (keys.coprod fresh))

end Lax342547.JointDirections
