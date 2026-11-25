import Lax793645Proofs.Simplifications.AffineQueryCorners

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A T : Type} [Fintype A] [Fintype T] [DecidableEq T]

def threeTuple (A : Type) : (Fin 3→A)≃(A×(A×A)) where
  toFun x:=(x 0,x 1,x 2)
  invFun x:=![x.1,x.2.1,x.2.2]
  left_inv x:=by funext i; fin_cases i <;> rfl
  right_inv _:=rfl

theorem three_average (F : A→A→A→ℝ) :
    avg unif (fun x : Fin 3→A=>F (x 0) (x 1) (x 2))=
      avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>F x y z))) := by
  have hh:=mapW_avg unif (threeTuple A) (fun x=>F x.1 x.2.1 x.2.2)
  rw [unif_equiv,pair_unif,pairW_avg] at hh
  rw [pair_unif] at hh
  simp_rw [pairW_avg] at hh
  exact hh.symm

def tripleFlatten (T A : Type) : (T→Fin 3→A)≃(T×Fin 3→A) where
  toFun x v:=x v.1 v.2
  invFun x t a:=x (t,a)
  left_inv _:=rfl
  right_inv _:=rfl

variable [Add A]
def additiveFourth (f : Wgt A) : ℝ :=
  avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>f x*f y*f z*f (x+y+z))))
def cornerValue (f : Wgt A) (x : Fin 3→A) : ℝ :=
  f (x 0)*f (x 1)*f (x 2)*f (x 0+x 1+x 2)

/-- Exact high-moment expansion in the original three input columns per
batch. It introduces no conditioning or nominal-independence assumption. -/
theorem repeated_additive_fourth (f : Wgt A) :
    (additiveFourth f)^Fintype.card T=
      avg unif (fun y : T×Fin 3→A=>∏ t:T,cornerValue f (fun a=>y (t,a))) := by
  have hq : avg unif (cornerValue f)=additiveFourth f:=three_average (fun x y z : A=>f x*f y*f z*f (x+y+z))
  have hh:=prodW_avg (fun _ : T=>(unif : Wgt (Fin 3→A))) (fun _=>cornerValue f)
  rw [←uniform_product_law] at hh
  simp only [hq,Finset.prod_const,card_univ] at hh
  have he:=mapW_avg unif (tripleFlatten T A)
    (fun y : T×Fin 3→A=>∏ t:T,cornerValue f (fun a=>y (t,a)))
  rw [unif_equiv] at he
  exact hh.symm.trans he.symm

omit [Fintype A] in
theorem corner_value_bound (f : Wgt A) (hf : ∀ x,|f x|≤1) (x : Fin 3→A) :
    |cornerValue f x|≤1 := by
  unfold cornerValue
  simp only [abs_mul]
  exact (mul_le_mul (mul_le_mul (mul_le_mul (hf _) (hf _) (abs_nonneg _) (by norm_num))
    (hf _) (abs_nonneg _) (by norm_num)) (hf _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

def queryFourth (v : Template p I) (D : Wgt (KeyCoordinates (KeySlots p v.t) N))
    (ψ : Wgt (Inputs p n I)) (o : UnitType p n N) : ℝ :=
  additiveFourth (fun x=>D (templateKeyCoordinates v o x)*ψ x)

def nominalCornerWeight (ψ : Wgt (Inputs p n I)) (y : T×Fin 3→Inputs p n I) : ℝ :=
  ∏ t:T,cornerValue ψ (fun a=>y (t,a))

omit [DecidableEq T] [Fintype I] [DecidableEq I] in
theorem nominal_corner_weight_bound (ψ : Wgt (Inputs p n I)) (hψ : ∀ x,|ψ x|≤1)
    (y : T×Fin 3→Inputs p n I) : |nominalCornerWeight ψ y|≤1 := by
  unfold nominalCornerWeight
  rw [Finset.abs_prod]
  exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun t _=>corner_value_bound ψ hψ _)).trans_eq (by simp)

/-- The nominal weight is fixed before the orientation is drawn. Its
entire four-corner product can be kept outside the raw-frame average. -/
theorem query_moment_expansion (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (ρ : Wgt (UnitType p n N)) :
    avg ρ (fun o=>(queryFourth v D ψ o)^Fintype.card T)=
      avg unif (fun y : T×Fin 3→Inputs p n I=>nominalCornerWeight ψ y*
        avg ρ (fun o=>∏ t:T,cornerProduct D
          (led t (peekR p (cornerRoute v T) (cornerNominal v y) (cornerNominal v y) (mergeR p o))))) := by
  have he (o : UnitType p n N) (y : T×Fin 3→Inputs p n I) :
      (∏ t:T,cornerValue (fun x=>D (templateKeyCoordinates v o x)*ψ x) (fun a=>y (t,a)))=
      nominalCornerWeight ψ y*(∏ t:T,cornerProduct D
        (led t (peekR p (cornerRoute v T) (cornerNominal v y) (cornerNominal v y) (mergeR p o)))) := by
    unfold nominalCornerWeight
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t _
    rw [corner_nominal_product]
    unfold cornerValue
    ring
  unfold queryFourth
  simp_rw [repeated_additive_fourth (T:=T),he]
  rw [avg_avg]
  simp_rw [avg_mul']

/-- The unconditioned query input law has exactly uniform free Z data. -/
theorem uniform_free_knobs :
    mapW (unif : Wgt (Knobs p.g n)) (freePart p)=unif := by
  let L : Knobs p.g n→ₗ[F] Vec (Fin n) :=
    { toFun := fun x : Knobs p.g n=>x Block.Z
      map_add' := fun _ _=>rfl
      map_smul' := fun _ _=>rfl }
  have hL : Surjective L := by
    intro x
    refine ⟨Pi.single Block.Z x, ?_⟩
    simp only [L,LinearMap.coe_mk,AddHom.coe_mk,Pi.single_eq_same]
  exact map_unif_surjective L hL

theorem uniform_corner_nominal_tail (v : Template p I) (d : ℕ) :
    pr unif (fun y : T×Fin 3→Inputs p n I=>∃ e,
      (cornerNominal v y e).rank+d≤Fintype.card (Port (cornerRoute v T) e))≤
      bp ((num (T×Fin 3)*num I-n)*d) := by
  have hh:=corner_nominal_kernel_tail (T:=T) (n:=n) v (fun _=>unif) (fun _=>unif_law)
    (fun _=>uniform_free_knobs) d
  simp only [draws,←uniform_product_law] at hh
  exact hh

end
end Lax793645Proofs.Simplifications
