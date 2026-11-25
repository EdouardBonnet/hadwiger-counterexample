import Lax793645Proofs.Simplifications.ReducedProfileRank
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.PolarRankBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n : ℕ} {r : Comp p.g×Bool→ℕ}

abbrev ReducedTerms (p : Shape) (r : Comp p.g×Bool→ℕ):=
  Fin p.J × (Σ e : Comp p.g×Bool,Fin (r e))
abbrev ReducedParts (p : Shape) (n : ℕ) (r : Comp p.g×Bool→ℕ):=
  ∀ e,Mat (Row p n) (Fin (r e))

def reducedFormCol (P : ReducedParts p n r) (d : ReducedArray p n) :
    Mat (Row p n) (ReducedTerms p r) :=fun i ⟨j,⟨e,k⟩⟩=>
  (if e.2 then (d (j,e.1))ᵀ*P e else d (j,e.1)*P e) i k

theorem reduced_form_true (P : ReducedParts p n r) (d : ReducedArray p n) (i j e k) :
    reducedFormCol P d i (j,⟨(e,true),k⟩)=((d (j,e))ᵀ*P (e,true)) i k:=rfl
theorem reduced_form_false (P : ReducedParts p n r) (d : ReducedArray p n) (i j e k) :
    reducedFormCol P d i (j,⟨(e,false),k⟩)=(d (j,e)*P (e,false)) i k:=rfl

theorem reduced_qmix_factors (hg : Odd p.g) (P Q : ReducedParts p n r)
    (l : Tag p.g) (d : ReducedDraw p n) (x : Profile p n)
    (hx : ∀ e b,reducedProfile x l e b=P (e,b)*(Q (e,b))ᵀ) :
    qmix (reducedMixer d) x l=reducedFormCol P d.1*(reducedFormCol Q d.2.1)ᵀ := by
  rw [reduced_qmix hg]
  have h (e b) (L R : Moment p n) :
      liftM L R (reducedProfile x l e b)=L*P (e,b)*(R*Q (e,b))ᵀ := by
    rw [liftM_def,hx]
    simp only [Matrix.mul_assoc,transpose_mul]
  ext i k
  simp only [Matrix.sum_apply]
  change _=∑ t:ReducedTerms p r,reducedFormCol P d.1 i t*reducedFormCol Q d.2.1 k t
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro j _
  rw [Fintype.sum_sigma,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro e _
  simp only [Matrix.add_apply,h,Fintype.sum_bool,reduced_form_true,reduced_form_false,
    Matrix.mul_apply,Matrix.transpose_apply]

theorem reduced_form_add (P : ReducedParts p n r) (d d' : ReducedArray p n) :
    reducedFormCol P (d+d')=reducedFormCol P d+reducedFormCol P d' := by
  ext i j
  rcases j with ⟨j,⟨⟨e,b⟩,k⟩⟩
  cases b <;> simp only [reducedFormCol,Matrix.add_apply,Pi.add_apply,if_true,if_false,
    Bool.false_eq_true,Matrix.add_mul,Matrix.transpose_add]

theorem reduced_form_smul (P : ReducedParts p n r) (a : F) (d : ReducedArray p n) :
    reducedFormCol P (a •d)=a •reducedFormCol P d := by
  ext i j
  rcases j with ⟨j,⟨⟨e,b⟩,k⟩⟩
  cases b <;> simp only [reducedFormCol,Matrix.smul_apply,Pi.smul_apply,if_true,if_false,
    Bool.false_eq_true,Matrix.smul_mul,Matrix.transpose_smul]

variable {U : Type} [Fintype U]

def reducedStack (P Q : ReducedParts p n r) (W : Mat (Row p n) U) :
    ReducedDraw p n→ₗ[F]Mat U (ReducedTerms p r⊕ReducedTerms p r) where
  toFun d:=Wᵀ*fromCols (reducedFormCol P d.1) (reducedFormCol Q d.2.1)
  map_add' d d':=by
    simp only [Prod.fst_add,Prod.snd_add,reduced_form_add,mul_fromCols,Matrix.mul_add]
    ext i j; cases j <;> rfl
  map_smul' a d:=by
    simp only [Prod.smul_fst,Prod.smul_snd,reduced_form_smul,mul_fromCols,RingHom.id_apply,
      Matrix.mul_smul]
    ext i j; cases j <;> rfl

theorem reduced_form_onto (P : ReducedParts p n r) (W : Mat (Row p n) U)
    (hw : Injective W.mulVec) (hP : ∀ e,Injective (P e).mulVec)
    (h : ∀ e,Disjoint (colSp (P e)) (colSp W)) (A : Mat U (ReducedTerms p r)) :
    ∃ d : ReducedArray p n,Wᵀ*reducedFormCol P d=A := by
  let tgt (j : Fin p.J) (e : Comp p.g) (b : Bool) : Mat (Fin (r (e,b))) U:=
    fun k i=>A i (j,⟨(e,b),k⟩)
  have ho (j : Fin p.J) (e : Comp p.g) :∃ L : Moment p n,
      (P (e,true))ᵀ*L*W=tgt j e true ∧ (P (e,false))ᵀ*Lᵀ*W=tgt j e false:=
    prescribe_opposite (inj_fromCols (hP _) hw (h _))
      (inj_fromCols hw (hP _) (h _).symm) _ _
  choose D hD hd using ho
  let d : ReducedArray p n:=fun ⟨j,e⟩=>D j e
  refine ⟨d,?_⟩
  ext i j
  rcases j with ⟨j,⟨⟨e,b⟩,k⟩⟩
  cases b
  · have he:Wᵀ*(D j e*P (e,false))=(tgt j e false)ᵀ := by
      rw [←hd]; simp only [transpose_mul,transpose_transpose,Matrix.mul_assoc]
    change (Wᵀ*(D j e*P (e,false))) i k=_
    rw [he]
    rfl
  have he:Wᵀ*((D j e)ᵀ*P (e,true))=(tgt j e true)ᵀ := by
    rw [←hD]; simp only [transpose_mul,transpose_transpose,Matrix.mul_assoc]
  change (Wᵀ*((D j e)ᵀ*P (e,true))) i k=_
  rw [he]
  rfl

theorem reduced_stack_surj (P Q : ReducedParts p n r) (W : Mat (Row p n) U)
    (hw : Injective W.mulVec) (hP : ∀ e,Injective (P e).mulVec)
    (hQ : ∀ e,Injective (Q e).mulVec)
    (h₁ : ∀ e,Disjoint (colSp (P e)) (colSp W))
    (h₂ : ∀ e,Disjoint (colSp (Q e)) (colSp W)) : Surjective (reducedStack P Q W) := by
  intro A
  obtain ⟨d,hd⟩:=reduced_form_onto P W hw hP h₁ A.toCols₁
  obtain ⟨f,hf⟩:=reduced_form_onto Q W hw hQ h₂ A.toCols₂
  refine ⟨(d,f,0),?_⟩
  change Wᵀ*fromCols (reducedFormCol P d) (reducedFormCol Q f)=_
  rw [mul_fromCols,hd,hf,fromCols_toCols]

end
end Lax793645Proofs.Simplifications
