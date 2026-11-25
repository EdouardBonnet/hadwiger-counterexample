import Lax793645Proofs.Simplifications.OneEffectiveSpaces
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.StatusCharts

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Module Submodule Function
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {d : Rates}

def oneCharted (v : Charts p n d) (a : ImagePlan (Comp p.g) (OneColumn p n)) :=
  ∀ i,LinearMap.range (v i)=oneEffectivePins (oneEndpointPrimalPins a) i ∧ Injective (v i)

theorem one_chart_create (a : ImagePlan (Comp p.g) (OneColumn p n)) :
    let d:=fun i=>dim (oneEffectivePins (oneEndpointPrimalPins a) i)
    ∃ v : Charts p n d,oneCharted v a := by
  intro d
  have hh (i) : ∃ f : Ax p n (d i),
      LinearMap.range f=oneEffectivePins (oneEndpointPrimalPins a) i ∧ Injective f := by
    let S:=oneEffectivePins (oneEndpointPrimalPins a) i
    let E : Cell (d i)≃ₗ[F]S:=LinearEquiv.ofFinrankEq _ _
      (by change dim (Cell (d i))=d i; rw [dim_vec,Fintype.card_fin])
    refine ⟨S.subtype ∘ₗ E.toLinearMap,?_,Subtype.val_injective.comp E.injective⟩
    rw [LinearMap.range_comp,LinearMap.range_eq_top.mpr E.surjective,
      ←LinearMap.range_eq_map,Submodule.range_subtype S]
  choose v hv using hh
  exact ⟨v,hv⟩

def oneSpecify (p : Shape) {d : ℕ} (i : Nodes) (v : Ax p n d)
    (m : Mixer p n) (o : OneUnit p n N) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (x : Knobs p.g n) : Magazine p d :=
  let A:=useAtom p l s f x
  (scan p l f x,(role p n A,roll v (Tsym m A)),oneInner o i A)

end
end Lax793645Proofs.Simplifications
