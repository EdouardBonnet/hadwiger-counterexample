import Lax793645Proofs.Simplifications.OneMultiRowBounds
import Lax793645Proofs.Simplifications.OneJointKeyFiberLaws
import Lax793645Proofs.Simplifications.OneQueryCorners
import Lax793645Proofs.Simplifications.OneChannelImageBounds
import Lax793645Proofs.Simplifications.LinearSlotRanks

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Module Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

abbrev OneSlotKeys (t : Tagging p I) (N : ℕ):=KeySlots p t→Vec (HyperbolicIdx N)

def oneSlotSlice (t : Tagging p I) (i : I) :
    OneSlotKeys t N→ₗ[F]OneJointKey p N:=LinearMap.pi
      (fun e=>if h:inc e (t i) then LinearMap.proj ⟨i,⟨e,h⟩⟩ else 0)

theorem one_slot_slice_at (t : Tagging p I) (i : I) (e : TagStar (t i))
    (x : OneSlotKeys t N) : oneSlotSlice t i x e.val=x ⟨i,e⟩ := by
  simp only [oneSlotSlice,LinearMap.pi_apply,dif_pos e.property,LinearMap.proj_apply]

def oneTupleFreeRows (v : Template p I) (o : OneUnit p n N) :
    OneSlotKeys v.t N→ₗ[F](I→Module.Dual F (Vec (Fin n))):=
  LinearMap.pi (fun i=>(oneMixedRow (oneFreeColumns p n (v.s i)) (o (v.aim i))).comp
    (oneSlotSlice v.t i))

theorem one_tuple_rows_zero_cap (v : Template p I) [Nonempty (KeySlots p v.t)]
    {D : Type} [AddCommGroup D] [Module F D] [FiniteDimensional F D]
    (m : Mixer p n) (d : ℕ)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 2*d+3≤N)
    (T : D→ₗ[F]OneSlotKeys v.t N) (hT : Injective T)
    (hd : Fintype.card (KeySlots p v.t)*d≤dim D) :
    pr (oneUnitRaw m N) (fun o=>(oneTupleFreeRows v o).comp T=0)≤
      bp ((d:ℝ)^2+2-d*n) := by
  obtain ⟨slot,hslot⟩:=linear_slot_large_rank T hT d hd
  obtain ⟨J,hJ⟩:=linear_rank_restriction ((LinearMap.proj slot).comp T) d hslot
  let S:=(oneSlotSlice v.t slot.1).comp (T.comp J)
  have hS : Injective ((LinearMap.proj slot.2.val).comp S) := by
    intro x y hxy
    apply hJ
    change T (J x) slot=T (J y) slot
    change oneSlotSlice v.t slot.1 (T (J x)) slot.2.val=
      oneSlotSlice v.t slot.1 (T (J y)) slot.2.val at hxy
    simpa only [one_slot_slice_at] using hxy
  have hb:=one_independent_rows m hroom hN
    (oneFreeColumns p n (v.s slot.1)) (one_free_columns_injective _) S slot.2.val hS 0
  have hproj : mapW (oneUnitRaw m N) (fun o=>o (v.aim slot.1))=oneRaw m N:=
    product_projection_law (fun _ : Bool=>oneRaw m N)
      (fun _=>one_raw_law m hroom) (v.aim slot.1)
  have hsub (o : OneUnit p n N) (h : (oneTupleFreeRows v o).comp T=0) :
      (oneMixedRow (oneFreeColumns p n (v.s slot.1)) (o (v.aim slot.1))).comp S=0 := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro z
    have hh:=congrFun (LinearMap.congr_fun h (J x)) slot.1
    exact LinearMap.congr_fun hh z
  have hc:=(pr_mono (one_unit_raw_law m hroom).nz hsub)
  have he := mapW_pr (oneUnitRaw m N) (fun o=>o (v.aim slot.1))
    (fun o=>(oneMixedRow (oneFreeColumns p n (v.s slot.1)) o).comp S=0)
  rw [hproj] at he
  rw [←he] at hc
  exact hc.trans hb

end
end Lax793645Proofs.Simplifications
