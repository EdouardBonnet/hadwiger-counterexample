import Lax793645Proofs.Simplifications.RawFrameBatchBound
import Lax793645Proofs.Simplifications.NominalKernelTails

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  {p : Shape} {n N : ℕ}

omit [Fintype I] [DecidableEq I] in
theorem lit_three (f : Flavor p.g) (l : Tag p.g) (x y z : Knobs p.g n) :
    lit f l (x+y+z)=lit f l x+lit f l y+lit f l z := by
  funext i
  by_cases h : f.keeps l i.1 <;> simp [lit,h]

theorem base_vector_three (x y z : Base p.g n) : baseV (x+y+z)=baseV x+baseV y+baseV z := by
  funext i
  cases i with
  | none =>
      change (1:F)=1+1+1
      rw [ZModModule.add_self,zero_add]
  | some i => rfl

theorem point_three (s : Label p.b) (x y z : Base p.g n) :
    point p s (x+y+z)=point p s x+point p s y+point p s z := by
  simp only [point,base_vector_three,map_add]

omit [Fintype I] [DecidableEq I] in
/-- Every fixed-orientation key map is affine over the binary field. -/
theorem template_key_three (v : Template p I) (o : UnitType p n N) (x y z : Inputs p n I) :
    (v.draw (x+y+z)).keys v.t o=(v.draw x).keys v.t o+(v.draw y).keys v.t o+(v.draw z).keys v.t o := by
  funext i e b
  change primary _*ᵥpoint p (v.s i) (lit (v.f i) (v.t i) (x i+y i+z i))=_
  rw [lit_three,point_three,Matrix.mulVec_add,Matrix.mulVec_add]
  rfl

def templateKeyCoordinates (v : Template p I) (o : UnitType p n N) (x : Inputs p n I) :
    KeyCoordinates (KeySlots p v.t) N :=
  (rackCoordinates (KeySlots p v.t) N).symm (scatter v.t N ((v.draw x).keys v.t o))

omit [Fintype I] [DecidableEq I] in
theorem template_coordinate_three (v : Template p I) (o : UnitType p n N) (x y z : Inputs p n I) :
    templateKeyCoordinates v o (x+y+z)=templateKeyCoordinates v o x+
      templateKeyCoordinates v o y+templateKeyCoordinates v o z := by
  rw [templateKeyCoordinates,template_key_three]
  funext c
  rcases c with ⟨u,b,i⟩
  cases b <;> rfl

def cornerRoute (v : Template p I) (T : Type) : Route (T×(Fin 3×KeySlots p v.t)) (Ports p) :=
  tied (tied (globPort p v.t v.aim) (Fin 3)) T

def cornerNominal (v : Template p I) (y : (T×Fin 3)→Inputs p n I) :
    NomQuery p n (cornerRoute v T) :=
  pooled (fun t=>pooled (fun a=>nomAsk v.t (v.draw (y (t,a)))))

omit [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] in
/-- The original nominal columns produce all three free corners. The
fourth is their affine sum, with no independent replacement sampling. -/
theorem corner_nominal_key (v : Template p I) (y : (T×Fin 3)→Inputs p n I)
    (o : UnitType p n N) (t : T) (a : Fin 3) :
    (rackCoordinates (KeySlots p v.t) N).symm
      (led a (led t (peekR p (cornerRoute v T) (cornerNominal v y) (cornerNominal v y) (mergeR p o))))=
      templateKeyCoordinates v o (y (t,a)) := by
  unfold cornerNominal cornerRoute
  rw [peek_pooled,peek_pooled]
  exact congrArg (rackCoordinates (KeySlots p v.t) N).symm
    (peek_keys v.t (v.draw (y (t,a))) o)

omit [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] in
theorem corner_nominal_product (v : Template p I) (y : (T×Fin 3)→Inputs p n I)
    (o : UnitType p n N) (t : T) (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) :
    cornerProduct D (led t (peekR p (cornerRoute v T) (cornerNominal v y) (cornerNominal v y) (mergeR p o)))=
      D (templateKeyCoordinates v o (y (t,0)))*D (templateKeyCoordinates v o (y (t,1)))*
      D (templateKeyCoordinates v o (y (t,2)))*
      D (templateKeyCoordinates v o (y (t,0)+y (t,1)+y (t,2))) := by
  unfold cornerProduct
  simp only [corner_nominal_key,template_coordinate_three]

omit [DecidableEq I] [DecidableEq T] in
/-- The repeated-query mask respects every ordered same-component Gram
quantity fixed by the reference key variety. -/
theorem corner_query_mask (v : Template p I) :
    ∀ x∈crowded (cornerRoute v T),(x.1.2.2,x.2.2.2)∈crowded (ownPort v.t) := by
  classical
  intro x hx
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  exact congrArg Prod.snd (mem_filter.mp hx).2

omit [Fintype I] [DecidableEq I] in
theorem query_port_injective (v : Template p I) (e : Ports p) :
    Injective (fun i : Port (globPort p v.t v.aim) e=>i.val.1) := by
  rintro ⟨⟨a,c⟩,ha⟩ ⟨⟨b,d⟩,hb⟩ he
  change a=b at he
  subst b
  have h : c=d:=Subtype.ext (congrArg Prod.snd (ha.trans hb.symm))
  subst d
  rfl

/-- Nominal relations in any component inject into the kernel of all the
fresh Z columns of the three-corner experiment. -/
theorem corner_nominal_kernel_dimension (v : Template p I)
    (y : (T×Fin 3)→Inputs p n I) (e : Ports p) :
    Fintype.card (Port (cornerRoute v T) e)-(cornerNominal v y e).rank≤
      Fintype.card ((T×Fin 3)×I)-(freeNet p y).rank := by
  classical
  let r : T×(Fin 3×KeySlots p v.t)→(T×Fin 3)×I:=fun x=>((x.1,x.2.1),x.2.2.1)
  have hr : Injective (fun a : Port (cornerRoute v T) e=>r a.val) := by
    rintro ⟨⟨t,c,a⟩,ha⟩ ⟨⟨t',c',b⟩,hb⟩ h
    have ht : t=t':=congrArg (fun x=>x.1.1) h
    have hc : c=c':=congrArg (fun x=>x.1.2) h
    have hk : a=b:=congrArg Subtype.val (query_port_injective v e (show
      (⟨a,ha⟩ : Port (globPort p v.t v.aim) e).val.1=
      (⟨b,hb⟩ : Port (globPort p v.t v.aim) e).val.1 from congrArg Prod.snd h))
    exact Subtype.ext (Prod.ext ht (Prod.ext hc hk))
  apply ray_kernel_dimension (b:=r) e (freeNet p y) hr
  intro a j
  change point p _ _ (emptySel,some (Block.Z,j))=freeNet p y j ((a.val.1,a.val.2.1),a.val.2.2.1)
  rw [point_base_eval]
  exact if_pos (Flavor.keepZ _ _)

/-- Large nominal deficiencies retain their exponential tail in the
actual three-corner query experiment. No corner factor is deleted. -/
theorem corner_nominal_kernel_tail (v : Template p I)
    (w : I→Wgt (Knobs p.g n)) (hl : ∀ i,IsLaw (w i))
    (hw : ∀ i,mapW (w i) (freePart p)=unif) (d : ℕ) :
    pr (draws (T×Fin 3) (prodW w)) (fun y=>∃ e,
      (cornerNominal v y e).rank+d≤Fintype.card (Port (cornerRoute v T) e))≤
      bp ((num (T×Fin 3)*num I-n)*d) := by
  refine (pr_mono (draws_law (prodW_law hl)).nz ?_).trans
    (free_nominal_kernel_tail (T:=T×Fin 3) p n w hw d)
  intro y hy
  obtain ⟨e,he⟩:=hy
  have hh:=corner_nominal_kernel_dimension v y e
  have hr:=(freeNet p y).rank_le_card_width
  omega

end
end Lax793645Proofs.Simplifications
