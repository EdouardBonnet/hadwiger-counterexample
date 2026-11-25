import Lax793645Proofs.Simplifications.OneQueryCorrelation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {J : Type} [Fintype J] [DecidableEq J] {N : ℕ}

def auxiliaryCoordinates (J : Type) (N : ℕ) :
    (KeyCoordinates J N × KeyCoordinates J N) ≃ₗ[F] KeyCoordinates (Bool×J) N where
  toFun x c:=if c.2.2.1 then x.2 (c.1,(c.2.1,c.2.2.2)) else x.1 (c.1,(c.2.1,c.2.2.2))
  invFun x:=(fun c=>x (c.1,(c.2.1,(false,c.2.2))),fun c=>x (c.1,(c.2.1,(true,c.2.2))))
  left_inv x:=rfl
  right_inv x:=by funext c; rcases c with ⟨u,b,a,j⟩; cases a <;> rfl
  map_add' x y:=by funext c; rcases c with ⟨u,b,a,j⟩; cases a <;> rfl
  map_smul' a x:=by funext c; rcases c with ⟨u,b,a,j⟩; cases a <;> rfl

def auxiliaryBlock (M : Mat (Bool×J) (Bool×J)) (a b : Bool) : Mat J J :=
  M.submatrix (fun j=>(a,j)) (fun j=>(b,j))

theorem auxiliary_gram_decomposition (M : Mat (Bool×J) (Bool×J))
    (x y : KeyCoordinates J N) :
    gramPrimitive M (auxiliaryCoordinates J N (x,y))=
      gramPrimitive (auxiliaryBlock M false false) x+
      crossGram (auxiliaryBlock M false true) (auxiliaryBlock M true false) N x y+
      gramPrimitive (auxiliaryBlock M true true) y := by
  simp only [cross_gram_apply,gramPrimitive,layer_form,mpair,LinearMap.coe_mk,AddHom.coe_mk]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib]
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  dsimp only [auxiliaryBlock,Matrix.submatrix,auxiliaryCoordinates,keyPlus,keyMinus]
  simp only [LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,Matrix.of_apply,
    Bool.false_eq_true,ite_false,ite_true]
  ac_rfl

theorem auxiliary_character (ξ : KeyCoordinates (Bool×J) N) (x y : KeyCoordinates J N) :
    vectorPhase ξ (auxiliaryCoordinates J N (x,y))=
      vectorPhase (fun c=>ξ (c.1,(c.2.1,(false,c.2.2)))) x*
      vectorPhase (fun c=>ξ (c.1,(c.2.1,(true,c.2.2)))) y := by
  unfold vectorPhase dotProduct
  rw [←wsign_add]
  congr 1
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_add_distrib]
  dsimp only [auxiliaryCoordinates,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk]
  ac_rfl

/-- An auxiliary batch either contributes a small original Fourier
coefficient, or a nonzero original--auxiliary pairing gives cancellation.
There is no four-corner expression. -/
theorem auxiliary_batch_fourier (E : Rail J)
    (D : Wgt (KeyCoordinates J N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1)
    (hF : ∀ A : Mat J J,Aᵀ=A→withinRail A E→∀ ξ,
      |linearFourier (fun x=>phasedBy A (rackCoordinates J N x)*D x) ξ|≤δ)
    (M : Mat (Bool×J) (Bool×J)) (hM : Mᵀ=M)
    (hm : withinRail (auxiliaryBlock M false false) E)
    (haux : auxiliaryBlock M true true=0)
    (ξ : KeyCoordinates (Bool×J) N) :
    |linearFourier (fun x=>phasedBy M (rackCoordinates (Bool×J) N x)*
      D ((auxiliaryCoordinates J N).symm x).1) ξ|≤δ+bp (-(N:ℝ)/2) := by
  let ξ₀ : KeyCoordinates J N:=fun c=>ξ (c.1,(c.2.1,(false,c.2.2)))
  let ξ₁ : KeyCoordinates J N:=fun c=>ξ (c.1,(c.2.1,(true,c.2.2)))
  let A:=auxiliaryBlock M false false
  let C:=auxiliaryBlock M false true
  let C':=auxiliaryBlock M true false
  let f x:=vectorPhase ξ₀ x*wsign (gramPrimitive A x)*D x
  let g y:=vectorPhase ξ₁ y
  have hb x : |f x|≤1:=by
    simp only [f,abs_mul,vectorPhase,wsign_abs,one_mul]
    exact hD x
  have hg y : |g y|≤1:=(wsign_abs _).le
  have he : linearFourier (fun x=>phasedBy M (rackCoordinates (Bool×J) N x)*
      D ((auxiliaryCoordinates J N).symm x).1) ξ=
      avg unif (fun y=>g y*avg unif (fun x=>f x*wsign (crossGram C C' N x y))) := by
    let V x:=vectorPhase ξ x*(phasedBy M (rackCoordinates (Bool×J) N x)*
      D ((auxiliaryCoordinates J N).symm x).1)
    have hh:=mapW_avg unif (auxiliaryCoordinates J N).toEquiv V
    rw [unif_equiv] at hh
    change avg unif V=_
    rw [hh,pair_unif,pairW_avg,avg_avg]
    apply avg_congr
    intro y _
    rw [←avg_mul']
    apply avg_congr
    intro x _
    dsimp only [V,LinearEquiv.coe_toEquiv]
    rw [LinearEquiv.symm_apply_apply,auxiliary_character]
    change (_*_)*(wsign (gramPrimitive M (auxiliaryCoordinates J N (x,y)))*D x)=_
    rw [auxiliary_gram_decomposition,haux]
    have hz : gramPrimitive (0 : Mat J J) y=0:=by simp [gramPrimitive,layer_form,mpair]
    rw [hz,add_zero,wsign_add]
    dsimp only [f,g,ξ₀,ξ₁,A,C,C']
    ring
  rw [he]
  by_cases hC : C=0
  · have hC' : C'=0:=by
      have hh : C'=Cᵀ:=by
        ext i j
        exact congrFun (congrFun hM (false,j)) (true,i)
      rw [hh,hC,Matrix.transpose_zero]
    have hz x y : crossGram C C' N x y=0:=by
      rw [cross_gram_apply,layer_form,layer_form,hC,hC']
      simp [mpair]
    simp only [hz,wsign_zero,mul_one,avg_mul,abs_mul]
    have hf : |avg unif f|≤δ:=by
      simpa only [f,linearFourier,phasedBy,gramPrimitive,rackCoordinates,
        LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,mul_assoc] using
        hF A
          (by ext i j; exact congrFun (congrFun hM (false,i)) (false,j)) hm ξ₀
    have hgb:=avg_bound1 unif_law g hg
    exact (mul_le_mul hgb hf (abs_nonneg _) (by norm_num)).trans
      (by simpa only [one_mul] using le_add_of_nonneg_right (bp_pos (-(N:ℝ)/2)).le)
  · have hr : N≤rk (crossGram C C' N):=cross_gram_rank_nonzero C C' (Or.inl hC)
    exact (walsh_bound (crossGram C C' N) f g hb hg).trans
      ((bp_le (by exact_mod_cast (show -(N:ℝ)/2≥-(rk (crossGram C C' N):ℝ)/2 from
        div_le_div_of_nonneg_right (neg_le_neg (by exact_mod_cast hr)) (by norm_num)))).trans
          (le_add_of_nonneg_left hδ))

theorem auxiliary_local_fourier (E : Rail J) (Z : Mat J J)
    (D : Wgt (KeyCoordinates J N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1) (hs : ∀ x,D x≠0→quadraticTraced E Z x)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (M : Mat (Bool×J) (Bool×J)) (hM : Mᵀ=M)
    (hm : withinRail (auxiliaryBlock M false false) E)
    (haux : auxiliaryBlock M true true=0)
    (ξ : KeyCoordinates (Bool×J) N) :
    |linearFourier (fun x=>phasedBy M (rackCoordinates (Bool×J) N x)*
      D ((auxiliaryCoordinates J N).symm x).1) ξ|≤δ+bp (-(N:ℝ)/2) :=
  auxiliary_batch_fourier E D δ hδ hD (quadratic_supported_fourier E Z D δ hs hF)
    M hM hm haux ξ

end
end Lax793645Proofs.Simplifications
