import Lax793645Proofs.Simplifications.OneQueryImages
import Lax793645Proofs.Simplifications.AffineQueryCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I T G : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Fintype G] [DecidableEq G] {p : Shape} {n N : ℕ}

theorem one_template_key_three (v : Template p I) (o : OneUnit p n N) (x y z : Inputs p n I) :
    oneVolleyKeys (v.draw (x+y+z)) v.t o=
      oneVolleyKeys (v.draw x) v.t o+oneVolleyKeys (v.draw y) v.t o+oneVolleyKeys (v.draw z) v.t o := by
  funext i e
  change onePrimal _ (point p (v.s i) (lit (v.f i) (v.t i) (x i+y i+z i)))=_
  rw [lit_three,point_three,map_add,map_add]
  rfl

def oneTemplateCoordinates (v : Template p I) (o : OneUnit p n N) (x : Inputs p n I) :
    KeyCoordinates (KeySlots p v.t) N:=
  (rackCoordinates (KeySlots p v.t) N).symm (oneScatter v.t N (oneVolleyKeys (v.draw x) v.t o))

theorem one_template_coordinate_three (v : Template p I) (o : OneUnit p n N) (x y z : Inputs p n I) :
    oneTemplateCoordinates v o (x+y+z)=oneTemplateCoordinates v o x+
      oneTemplateCoordinates v o y+oneTemplateCoordinates v o z := by
  rw [oneTemplateCoordinates,one_template_key_three]
  funext c
  rcases c with ⟨u,b,i⟩
  cases b <;> rfl

theorem one_peek_plus (g : Route I G) (A : NomQuery p n g) (x : OneForum p n N G)
    (u : Fin N) (i : I) :
    (onePeek g A x).1 u i=onePrimal (x (g i)) ((A (g i)).col ⟨i,rfl⟩) (Sum.inl u) := by
  change onePrimal _ (A (g i)*ᵥPi.single ⟨i,rfl⟩ 1) (Sum.inl u)=_
  rw [Matrix.mulVec_single_one]

theorem one_peek_minus (g : Route I G) (A : NomQuery p n g) (x : OneForum p n N G)
    (u : Fin N) (i : I) :
    (onePeek g A x).2 u i=onePrimal (x (g i)) ((A (g i)).col ⟨i,rfl⟩) (Sum.inr u) := by
  change onePrimal _ (A (g i)*ᵥPi.single ⟨i,rfl⟩ 1) (Sum.inr u)=_
  rw [Matrix.mulVec_single_one]

theorem one_peek_pooled (g : Route I G) (A : T → NomQuery p n g) (x : OneForum p n N G) (i : T) :
    led i (onePeek (tied g T) (pooled A) x)=onePeek g (A i) x := by
  apply Prod.ext
  · ext u j
    change (onePeek (tied g T) (pooled A) x).1 u (i,j)=(onePeek g (A i) x).1 u j
    rw [one_peek_plus,one_peek_plus]
    rfl
  · ext u j
    change (onePeek (tied g T) (pooled A) x).2 u (i,j)=(onePeek g (A i) x).2 u j
    rw [one_peek_minus,one_peek_minus]
    rfl

theorem one_corner_nominal_key (v : Template p I) [DecidableEq (KeySlots p v.t)] (y : (T×Fin 3) → Inputs p n I)
    (o : OneUnit p n N) (t : T) (a : Fin 3) :
    (rackCoordinates (KeySlots p v.t) N).symm
      (led a (led t (onePeek (cornerRoute v T) (cornerNominal v y) (oneMerge o))))=
      oneTemplateCoordinates v o (y (t,a)) := by
  funext c
  rcases c with ⟨u,b,i⟩
  cases b
  · change onePrimal (o (v.aim i.1) i.2.val)
      ((cornerNominal v y (v.aim i.1,i.2.val))*ᵥPi.single ⟨(t,a,i),rfl⟩ 1) (Sum.inl u)=_
    rw [Matrix.mulVec_single_one]
    rfl
  · change onePrimal (o (v.aim i.1) i.2.val)
      ((cornerNominal v y (v.aim i.1,i.2.val))*ᵥPi.single ⟨(t,a,i),rfl⟩ 1) (Sum.inr u)=_
    rw [Matrix.mulVec_single_one]
    rfl

theorem one_corner_nominal_product (v : Template p I) [DecidableEq (KeySlots p v.t)] (y : (T×Fin 3) → Inputs p n I)
    (o : OneUnit p n N) (t : T) (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) :
    cornerProduct D (led t (onePeek (cornerRoute v T) (cornerNominal v y) (oneMerge o)))=
      D (oneTemplateCoordinates v o (y (t,0)))*D (oneTemplateCoordinates v o (y (t,1)))*
      D (oneTemplateCoordinates v o (y (t,2)))*
      D (oneTemplateCoordinates v o (y (t,0)+y (t,1)+y (t,2))) := by
  unfold cornerProduct
  simp only [one_corner_nominal_key,one_template_coordinate_three]

end
end Lax793645Proofs.Simplifications
