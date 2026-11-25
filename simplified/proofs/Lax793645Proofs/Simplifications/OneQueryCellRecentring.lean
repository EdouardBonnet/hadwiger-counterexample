import Lax793645Proofs.Simplifications.OneJointKeyFiberLaws
import Lax793645Proofs.Simplifications.QueryCellRecentring

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def oneQueryCellLinear (H : Space (OneJointKey p N)) (o : OneOrient p n N)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) :
    Knobs p.g n→ₗ[F]Module.Dual F H:=
  (oneJointCell H).comp ((onePrimalKey o).comp (springLinear p l s f))

theorem one_query_cell_affine (H : Space (OneJointKey p N)) (o : OneOrient p n N)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) (x : Knobs p.g n) :
    oneQueryCell H o l s f x=oneQueryCellLinear H o l s f x+oneQueryCell H o l s f 0 := by
  simp only [oneQueryCellLinear,LinearMap.comp_apply,springLinear,LinearMap.coe_mk,
    AddHom.coe_mk,map_sub,sub_add_cancel,oneQueryCell]

theorem one_query_cell_add_free (H : Space (OneJointKey p N))
    (o : OneOrient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) (z : Vec (Fin n)) :
    oneQueryCell H o l s f (x+freeKnob p n z)=oneQueryCell H o l s f x+
      ((oneJointCell H).comp (oneFreeKey (oneFreeColumns p n s) o)) z := by
  unfold oneQueryCell
  rw [spring_add_free,map_add,map_add,one_primal_key_free]
  rfl

def oneRecenterQuery (H : Space (OneJointKey p N)) (o : OneOrient p n N)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n)) (x : Knobs p.g n) (c : Module.Dual F H) :=
  x+freeKnob p n (S (c-oneQueryCell H o l s f x))

theorem one_recenter_query_eq (H : Space (OneJointKey p N))
    (o : OneOrient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n)) (x : Knobs p.g n) (c : Module.Dual F H) :
    oneRecenterQuery H o l s f S x c=
      affineRecenter (oneQueryCellLinear H o l s f) (oneQueryCell H o l s f 0)
        ((freeKnob p n).comp S) x c := by
  unfold oneRecenterQuery affineRecenter
  rw [one_query_cell_affine H o l s f x]
  rfl

theorem one_recenter_query_compound (H : Space (OneJointKey p N))
    (o : OneOrient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n)) (x : I→Knobs p.g n)
    (u : Vec I) (hu : weightsAff u) (c : Module.Dual F H) :
    compound p (fun i=>oneRecenterQuery H o l s f S (x i) c) u=
      oneRecenterQuery H o l s f S (compound p x u) c := by
  simp_rw [one_recenter_query_eq]
  exact affine_recenter_combination _ _ _ x u hu c

theorem one_recenter_query_cell (H : Space (OneJointKey p N))
    (o : OneOrient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n))
    (hS : ∀ c,((oneJointCell H).comp (oneFreeKey (oneFreeColumns p n s) o)) (S c)=c)
    (x : Knobs p.g n) (c : Module.Dual F H) :
    oneQueryCell H o l s f (oneRecenterQuery H o l s f S x c)=c := by
  rw [oneRecenterQuery,one_query_cell_add_free,hS,add_sub_cancel]

theorem one_recenter_query_punches (H : Space (OneJointKey p N))
    (o : OneOrient p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (S : Module.Dual F H→ₗ[F]Vec (Fin n)) (x : Knobs p.g n) (c : Module.Dual F H) :
    punchField p (oneRecenterQuery H o l s f S x c)=punchField p x := punch_add_free _ _

theorem one_recenter_query_uniform (H : Space (OneJointKey p N))
    [Fintype (Module.Dual F H)] (o : OneOrient p n N) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (S : Module.Dual F H→ₗ[F]Vec (Fin n)) :
    mapW (pairW unif unif) (fun x : Knobs p.g n×Module.Dual F H=>
      oneRecenterQuery H o l s f S x.1 x.2)=spins p n := by
  simp_rw [one_recenter_query_eq]
  rw [affine_recenter_uniform,spins,←draws_unif]

end
end Lax793645Proofs.Simplifications
