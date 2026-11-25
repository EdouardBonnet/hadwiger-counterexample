import Lax793645Proofs.Simplifications.OneQueryCorners
import Lax793645Proofs.Simplifications.QueryMomentExpansion

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  {p : Shape} {n N : ℕ}

def oneQueryFourth (v : Template p I) (D : Wgt (KeyCoordinates (KeySlots p v.t) N))
    (ψ : Wgt (Inputs p n I)) (o : OneUnit p n N) : ℝ :=
  additiveFourth (fun x=>D (oneTemplateCoordinates v o x)*ψ x)

/-- The nominal weight is fixed before the orientation is drawn. Its
entire four-corner product can be kept outside the raw-frame average. -/
theorem one_query_moment_expansion (v : Template p I) [DecidableEq (KeySlots p v.t)]
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (ρ : Wgt (OneUnit p n N)) :
    avg ρ (fun o=>(oneQueryFourth v D ψ o)^Fintype.card T)=
      avg unif (fun y : T×Fin 3→Inputs p n I=>nominalCornerWeight ψ y*
        avg ρ (fun o=>∏ t:T,cornerProduct D
          (led t (onePeek (cornerRoute v T) (cornerNominal v y) (oneMerge o))))) := by
  have he (o : OneUnit p n N) (y : T×Fin 3→Inputs p n I) :
      (∏ t:T,cornerValue (fun x=>D (oneTemplateCoordinates v o x)*ψ x) (fun a=>y (t,a)))=
      nominalCornerWeight ψ y*(∏ t:T,cornerProduct D
        (led t (onePeek (cornerRoute v T) (cornerNominal v y) (oneMerge o)))) := by
    unfold nominalCornerWeight
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t _
    rw [one_corner_nominal_product]
    unfold cornerValue
    ring
  unfold oneQueryFourth
  simp_rw [repeated_additive_fourth (T:=T),he]
  rw [avg_avg]
  simp_rw [avg_mul']

end
end Lax793645Proofs.Simplifications
