import Lax342547.JointDirections
import Lax342547Proofs.LeafImages

namespace Lax342547Proofs.JointDirections
open Lax342547.JointDirections

set_option backward.isDefEq.respectTransparency false
open Lax342547.MomentSpace

/--
---
conclusion: Lax342547.JointDirections.appended_quotient_injective
---
-/
theorem appended_quotient_injective {U V W : Type}
    [AddCommGroup U] [Module Binary U] [AddCommGroup V] [Module Binary V]
    [AddCommGroup W] [Module Binary W]
    (P : Submodule Binary W) (keys : U →ₗ[Binary] W) (fresh : V →ₗ[Binary] W)
    (hkeys : Function.Injective (P.mkQ.comp keys))
    (hfresh : Function.Injective ((P ⊔ LinearMap.range keys).mkQ.comp fresh)) :
    Function.Injective (P.mkQ.comp (keys.coprod fresh)) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · rintro ⟨u,v⟩ huv
    have hp : keys u + fresh v ∈ P := (Submodule.Quotient.mk_eq_zero _).mp huv
    have hfv : fresh v ∈ P ⊔ LinearMap.range keys := by
      have hsum : keys u + fresh v ∈ P ⊔ LinearMap.range keys := (show P ≤ P ⊔ LinearMap.range keys from le_sup_left) hp
      have hku : keys u ∈ P ⊔ LinearMap.range keys := (show LinearMap.range keys ≤ P ⊔ LinearMap.range keys from le_sup_right) (LinearMap.mem_range_self keys u)
      simpa only [add_sub_cancel_left] using (P ⊔ LinearMap.range keys).sub_mem hsum hku
    have hv : v = 0 := hfresh (show (P ⊔ LinearMap.range keys).mkQ (fresh v) =
        (P ⊔ LinearMap.range keys).mkQ (fresh 0) by
      have hz : (P ⊔ LinearMap.range keys).mkQ (fresh v) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hfv
      rw [hz, map_zero, map_zero])
    subst v
    have hku : keys u ∈ P := by simpa only [map_zero, add_zero] using hp
    have hu : u = 0 := hkeys (show P.mkQ (keys u) = P.mkQ (keys 0) by
      have hz : P.mkQ (keys u) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hku
      rw [hz, map_zero, map_zero])
    subst u
    exact Submodule.zero_mem _
  · exact bot_le

end Lax342547Proofs.JointDirections
