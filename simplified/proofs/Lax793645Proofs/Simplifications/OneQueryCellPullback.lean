import Lax793645Proofs.Simplifications.OneSlotPairings
import Lax793645Proofs.Simplifications.LinearRankCellBounds
import Lax793645Proofs.Simplifications.QueryCellRecentring

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset Matrix
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I W : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

def oneSlotCoordinates (t : Tagging p I) (N : ℕ) :
    OneSlotKeys t N≃ₗ[F]KeyCoordinates (KeySlots p t) N where
  toFun x:=fun ⟨a,b,s⟩=>if b then x s (Sum.inr a) else x s (Sum.inl a)
  invFun x s:=Sum.elim (fun a=>x (a,false,s)) (fun a=>x (a,true,s))
  left_inv x:=by funext s a; cases a <;> rfl
  right_inv x:=by funext ⟨a,b,s⟩; cases b <;> rfl
  map_add' x y:=by funext ⟨a,b,s⟩; cases b <;> rfl
  map_smul' c x:=by funext ⟨a,b,s⟩; cases b <;> rfl

def oneSlotValues (v : Template p I) (o : OneUnit p n N) (x : Inputs p n I) :
    OneSlotKeys v.t N:=fun s=>onePrimal (o (v.aim s.1) s.2.val)
      (spring p (v.t s.1) (v.s s.1) (v.f s.1) (x s.1))

theorem one_slot_values_coordinates (v : Template p I) (o : OneUnit p n N)
    (x : Inputs p n I) : oneSlotCoordinates v.t N (oneSlotValues v o x)=
      oneTemplateCoordinates v o x := by
  funext ⟨a,b,s⟩
  cases b <;> rfl

theorem one_slot_values_add_free (v : Template p I) (o : OneUnit p n N)
    (x : Inputs p n I) (z : I→Vec (Fin n)) :
    oneSlotValues v o (x+fun i=>freeKnob p n (z i))=
      oneSlotFreeColumns v o z+oneSlotValues v o x := by
  funext s
  change onePrimal (o (v.aim s.1) s.2.val)
    (spring p (v.t s.1) (v.s s.1) (v.f s.1) (x s.1+freeKnob p n (z s.1)))=_
  rw [spring_add_free,map_add]
  exact add_comm _ _

def onePartitionRows (t : Tagging p I) [DecidableEq (KeySlots p t)]
    (L : OneSlotKeys t N→ₗ[F]W) : Module.Dual F L.range→ₗ[F]OneSlotKeys t N:=
  (hyperbolicSlotPairing.toDual hyperbolic_slot_pairing_nondegenerate).symm.toLinearMap.comp
    L.rangeRestrict.dualMap

theorem one_partition_rows_injective (t : Tagging p I) [DecidableEq (KeySlots p t)]
    (L : OneSlotKeys t N→ₗ[F]W) : Injective (onePartitionRows t L) :=
  (hyperbolicSlotPairing.toDual hyperbolic_slot_pairing_nondegenerate).symm.injective.comp
    (LinearMap.dualMap_injective_of_surjective L.surjective_rangeRestrict)

theorem one_partition_rows_cancel (t : Tagging p I) [DecidableEq (KeySlots p t)]
    (L : OneSlotKeys t N→ₗ[F]W) :
    LinearMap.comp hyperbolicSlotPairing (onePartitionRows t L)=L.rangeRestrict.dualMap := by
  apply LinearMap.ext
  intro x
  exact (hyperbolicSlotPairing.toDual hyperbolic_slot_pairing_nondegenerate).apply_symm_apply
    (L.rangeRestrict.dualMap x)

theorem one_partition_deficit (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (o : OneUnit p n N) (L : OneSlotKeys v.t N→ₗ[F]W) :
    ((oneSlotFreeColumns v o).dualMap.comp L.rangeRestrict.dualMap).ker=
      ((oneTupleFreeRows v o).comp (onePartitionRows v.t L)).ker := by
  rw [←one_slot_row_kernel,LinearMap.comp_assoc,one_partition_rows_cancel]

theorem one_uniform_query_cell [Fintype W] (v : Template p I)
    [DecidableEq (KeySlots p v.t)] (o : OneUnit p n N)
    (L : OneSlotKeys v.t N→ₗ[F]W) (d : ℕ)
    (hd : dim (((oneTupleFreeRows v o).comp (onePartitionRows v.t L)).ker)≤d) (w : W) :
    pr unif (fun x=>L (oneSlotValues v o x)=w)≤bp (d:ℝ)*mapW unif L w := by
  refine uniform_free_cell_cap (U:=Inputs p n I) (Z:=I→Vec (Fin n))
    (V:=OneSlotKeys v.t N) (W:=W)
    (oneSlotValues v o) (fun z i=>freeKnob p n (z i))
    (oneSlotFreeColumns v o) (one_slot_values_add_free v o) L d ?_ w
  rw [one_partition_deficit]
  exact hd

end
end Lax793645Proofs.Simplifications
