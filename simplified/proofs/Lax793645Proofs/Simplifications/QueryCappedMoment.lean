import Lax793645Proofs.Simplifications.QueryHighMoment

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

def inputCoordinates (p : Shape) (n : ℕ) (I : Type) :
    Vec (I×Block p.g×Fin n)≃ₗ[F] Inputs p n I where
  toFun x i b k:=x (i,b,k)
  invFun x v:=x v.1 v.2.1 v.2.2
  left_inv _:=rfl
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def inputFourierNorm (w : Wgt (Inputs p n I)) : ℝ:=
  fourierNorm (fun x=>w (inputCoordinates p n I x))

theorem input_average (f : Wgt (Inputs p n I)) :
    avg unif (fun x=>f (inputCoordinates p n I x))=avg unif f := by
  have hh:=mapW_avg unif (inputCoordinates p n I).toEquiv f
  rw [unif_equiv] at hh
  exact hh.symm

theorem input_fourth (f : Wgt (Inputs p n I)) :
    additiveFourth (fun x=>f (inputCoordinates p n I x))=additiveFourth f := by
  let e:=inputCoordinates p n I
  have ha (x y z : Vec (I×Block p.g×Fin n)) : e (x+y+z)=e x+e y+e z := by
    rw [map_add,map_add]
  have hz (x y : Vec (I×Block p.g×Fin n)) :
      avg unif (fun z=>f (e x)*f (e y)*f (e z)*f (e x+e y+e z))=
        avg unif (fun z=>f (e x)*f (e y)*f z*f (e x+e y+z)) :=
    input_average (fun z=>f (e x)*f (e y)*f z*f (e x+e y+z))
  have hy (x : Vec (I×Block p.g×Fin n)) :
      avg unif (fun y=>avg unif (fun z=>f (e x)*f (e y)*f z*f (e x+e y+z)))=
        avg unif (fun y=>avg unif (fun z=>f (e x)*f y*f z*f (e x+y+z))) :=
    input_average (fun y=>avg unif (fun z=>f (e x)*f y*f z*f (e x+y+z)))
  change avg unif (fun x=>avg unif (fun y=>avg unif (fun z=>
    f (e x)*f (e y)*f (e z)*f (e (x+y+z)))))=_
  simp_rw [ha,hz,hy]
  exact input_average (fun x=>avg unif (fun y=>avg unif (fun z=>f x*f y*f z*f (x+y+z))))

theorem query_fourth_nonneg (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (o : UnitType p n N) : 0≤queryFourth v D ψ o := by
  have hh:=four_corner_nonneg (fun x=>D (templateKeyCoordinates v o (inputCoordinates p n I x))*
    ψ (inputCoordinates p n I x))
  change 0≤additiveFourth (fun x=>(fun y=>D (templateKeyCoordinates v o y)*ψ y)
    (inputCoordinates p n I x)) at hh
  rw [input_fourth (fun y=>D (templateKeyCoordinates v o y)*ψ y)] at hh
  exact hh

/-- The weight may depend on the entire orientation. The key test and
nominal phase remain fixed before drawing from the capped leaf. -/
theorem query_capped_moment (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (μ π : Wgt (UnitType p n N)) (w : UnitType p n N→Wgt (Inputs p n I))
    (b C : ℝ) (hπ : ∀ o,0≤π o) (hcap : ∀ o,π o≤C*μ o)
    (hb : 0≤b) (hw : ∀ o,inputFourierNorm (w o)≤b) (ℓ : ℕ) :
    avg π (fun o=>|avg unif (fun x=>D (templateKeyCoordinates v o x)*ψ x*w o x)|^(4*ℓ))≤
      C*b^(4*ℓ)*avg μ (fun o=>(queryFourth v D ψ o)^ℓ) := by
  have hh:=capped_fourier_weight_moment μ π
    (fun o x=>D (templateKeyCoordinates v o (inputCoordinates p n I x))*ψ (inputCoordinates p n I x))
    (fun o x=>w o (inputCoordinates p n I x)) b C hπ hcap hb hw ℓ
  change avg π (fun o=>|avg unif (fun x=>(fun y=>D (templateKeyCoordinates v o y)*ψ y*w o y)
    (inputCoordinates p n I x))|^(4*ℓ))≤C*b^(4*ℓ)*avg μ (fun o=>
    (additiveFourth (fun x=>(fun y=>D (templateKeyCoordinates v o y)*ψ y)
      (inputCoordinates p n I x)))^ℓ) at hh
  have he o:=input_average (fun y=>D (templateKeyCoordinates v o y)*ψ y*w o y)
  have hq o:=input_fourth (fun y=>D (templateKeyCoordinates v o y)*ψ y)
  simp_rw [he,hq] at hh
  exact hh

/-- An explicit exceptional-mass estimate under a capped leaf. There is
no enumeration of the orientation-dependent input weights. -/
theorem query_capped_exception (v : Template p I)
    (D : Wgt (KeyCoordinates (KeySlots p v.t) N)) (ψ : Wgt (Inputs p n I))
    (μ π : Wgt (UnitType p n N)) (w : UnitType p n N→Wgt (Inputs p n I))
    (b C : ℝ) (hπ : ∀ o,0≤π o) (hcap : ∀ o,π o≤C*μ o)
    (hb : 0≤b) (hw : ∀ o,inputFourierNorm (w o)≤b) (ℓ : ℕ)
    (ε : ℝ) (hε : 0≤ε) :
    ε^(4*ℓ)*pr π (fun o=>ε≤|avg unif
      (fun x=>D (templateKeyCoordinates v o x)*ψ x*w o x)|)≤
      C*b^(4*ℓ)*avg μ (fun o=>(queryFourth v D ψ o)^ℓ) := by
  let f (o : UnitType p n N):=|avg unif
    (fun x=>D (templateKeyCoordinates v o x)*ψ x*w o x)|
  have hm:=le_avg_markov (w:=π) (f:=fun o=>f o^(4*ℓ)) hπ
    (fun o=>pow_nonneg (abs_nonneg _) _) (ε^(4*ℓ))
  have hp : pr π (fun o=>ε≤f o)≤pr π (fun o=>ε^(4*ℓ)≤f o^(4*ℓ)) :=
    pr_mono hπ (fun o h=>pow_le_pow_left₀ hε h _)
  exact (mul_le_mul_of_nonneg_left hp (pow_nonneg hε _)).trans
    (hm.trans (query_capped_moment v D ψ μ π w b C hπ hcap hb hw ℓ))

end
end Lax793645Proofs.Simplifications
