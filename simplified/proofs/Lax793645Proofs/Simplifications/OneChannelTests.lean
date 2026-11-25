import Lax793645Proofs.Simplifications.OneGramHits
import Lax793645Proofs.Simplifications.QuadraticTableCoordinates

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev OneCheckSide (p : Shape) (n : ℕ) :=
  Bool→Comp p.g→JointRay p n→ₗ[F]Hyperbolic p.h
abbrev OneCheckGram (p : Shape) (n : ℕ) := OneCheckSide p n×OneCheckSide p n

instance oneCheckSideFintype (p : Shape) (n : ℕ) : Fintype (OneCheckSide p n) := by
  classical
  letI : Fintype (JointRay p n→ₗ[F]Hyperbolic p.h):=
    Fintype.ofInjective (fun f : JointRay p n→ₗ[F]Hyperbolic p.h=>⇑f) DFunLike.coe_injective
  infer_instance

variable {p : Shape} {n N : ℕ}

theorem one_table_cross_add (Q R : OneCross p n) (e : Comp p.g) :
    oneTableOfCross (Q+R) e=oneTableOfCross Q e+oneTableOfCross R e := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  simp only [oneTableOfCross,Pi.add_apply,map_add,LinearMap.compl₁₂_apply,LinearMap.add_apply]

theorem one_table_cross_smul (c : F) (Q : OneCross p n) (e : Comp p.g) :
    oneTableOfCross (c • Q) e=c • oneTableOfCross Q e := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  simp only [oneTableOfCross,Pi.smul_apply,map_smul,LinearMap.compl₁₂_apply,LinearMap.smul_apply]

def oneChannelTest : OneCross p n→ₗ[F]OneCheckGram p n where
  toFun Q:=(fun j e=>unitLeftChannels p.h (oneTableOfCross Q e) j,
    fun i e=>unitRightChannels p.h (oneTableOfCross Q e) i)
  map_add' Q R:=by
    apply Prod.ext <;> funext i e <;> apply LinearMap.ext <;> intro v
    · apply (LinearMap.BilinForm.toDual (hyperbolicQuadratic p.h).polarBilin (hyperbolic_nondegenerate p.h)).injective
      apply LinearMap.ext
      intro c
      change (hyperbolicQuadratic p.h).polarBilin _ c=(hyperbolicQuadratic p.h).polarBilin _ c
      simp only [Prod.fst_add,Pi.add_apply,map_add,LinearMap.add_apply,unit_left_channels_pairing,one_table_cross_add]
    · apply (LinearMap.BilinForm.toDual (hyperbolicQuadratic p.h).polarBilin (hyperbolic_nondegenerate p.h)).injective
      apply LinearMap.ext
      intro c
      change (hyperbolicQuadratic p.h).polarBilin _ c=(hyperbolicQuadratic p.h).polarBilin _ c
      simp only [Prod.snd_add,Pi.add_apply,unitRightChannels,map_add,LinearMap.add_apply,unit_left_channels_pairing,
        LinearMap.flip_apply,one_table_cross_add]
  map_smul' c Q:=by
    apply Prod.ext <;> funext i e <;> apply LinearMap.ext <;> intro v
    · apply (LinearMap.BilinForm.toDual (hyperbolicQuadratic p.h).polarBilin (hyperbolic_nondegenerate p.h)).injective
      apply LinearMap.ext
      intro d
      change (hyperbolicQuadratic p.h).polarBilin _ d=(hyperbolicQuadratic p.h).polarBilin _ d
      simp only [Prod.smul_fst,Pi.smul_apply,map_smul,LinearMap.smul_apply,unit_left_channels_pairing,one_table_cross_smul,RingHom.id_apply]
    · apply (LinearMap.BilinForm.toDual (hyperbolicQuadratic p.h).polarBilin (hyperbolic_nondegenerate p.h)).injective
      apply LinearMap.ext
      intro d
      change (hyperbolicQuadratic p.h).polarBilin _ d=(hyperbolicQuadratic p.h).polarBilin _ d
      simp only [Prod.smul_snd,Pi.smul_apply,unitRightChannels,map_smul,LinearMap.smul_apply,unit_left_channels_pairing,
        LinearMap.flip_apply,one_table_cross_smul,RingHom.id_apply]

theorem one_channel_test_dimension :
    dim (OneCheckGram p n)=16*Fintype.card (Comp p.g)*p.h*Fintype.card (Row p n) := by
  classical
  simp only [dim,OneCheckGram,OneCheckSide,Module.finrank_prod,Module.finrank_pi_fintype,
    Module.finrank_linearMap,JointRay,Vec,Hyperbolic,Module.finrank_self,
    Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool]
  ring

/-- The collision test records exactly the reciprocal primal-channel
maps. Primal-primal and channel-channel entries need not be prescribed. -/
theorem one_test_actual_channels (x y : OneUnit p n N) (Q : OneCross p n)
    (ht : oneChannelTest (oneCrossMatrix x y)=oneChannelTest Q) :
    ∀ e a b,oneUnitActual x y e a b=
      unitQuadraticTable p.h (unitPrimalTable p.h (oneUnitActual x y e))
        (unitChannelTable p.h (oneUnitActual x y e))
        (fun j=>unitLeftChannels p.h (oneTableOfCross Q e) j)
        (fun i=>unitRightChannels p.h (oneTableOfCross Q e) i) a b := by
  intro e a b
  have hL (j : Bool) : unitLeftChannels p.h (oneUnitActual x y e) j=
      unitLeftChannels p.h (oneTableOfCross Q e) j := by
    have hh:=congrFun (congrFun (congrArg Prod.fst ht) j) e
    change unitLeftChannels p.h (oneTableOfCross (oneCrossMatrix x y) e) j=_ at hh
    rwa [one_actual_table] at hh
  have hR (i : Bool) : unitRightChannels p.h (oneUnitActual x y e) i=
      unitRightChannels p.h (oneTableOfCross Q e) i := by
    have hh:=congrFun (congrFun (congrArg Prod.snd ht) i) e
    change unitRightChannels p.h (oneTableOfCross (oneCrossMatrix x y) e) i=_ at hh
    rwa [one_actual_table] at hh
  rw [←funext hL,←funext hR,unit_table_coordinates]

end
end Lax793645Proofs.Simplifications
