import Lax793645Proofs.Simplifications.GramPatternSum

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] {N : ℕ}

def cornerRack (I : Type) (N : ℕ) : Vec (CornerCoordinates I N)≃ₗ[F] Rack (Fin 3×I) N where
  toFun x := ((fun u i=>x (i.1,(u,(false,i.2)))),(fun u i=>x (i.1,(u,(true,i.2)))))
  invFun z c := if c.2.2.1 then z.2 c.2.1 (c.1,c.2.2.2) else z.1 c.2.1 (c.1,c.2.2.2)
  left_inv x := by funext c; rcases c with ⟨a,u,b,i⟩; cases b <;> rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq I] in
theorem corner_rack_character (ξ : KeyCoordinates (Fin 3×I) N) (x : Vec (CornerCoordinates I N)) :
    vectorPhase ξ ((rackCoordinates (Fin 3×I) N).symm (cornerRack I N x))=
      vectorPhase (fun c : CornerCoordinates I N=>ξ (c.2.1,(c.2.2.1,(c.1,c.2.2.2)))) x := by
  unfold vectorPhase dotProduct
  simp only [Fintype.sum_prod_type]
  congr 1
  have he u : (∑ b:Bool,∑ a:Fin 3,∑ i:I,ξ (u,(b,(a,i)))*
      ((rackCoordinates (Fin 3×I) N).symm (cornerRack I N x)) (u,(b,(a,i))))=
      ∑ a:Fin 3,∑ b:Bool,∑ i:I,ξ (u,(b,(a,i)))*x (a,(u,(b,i))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    cases b <;> rfl
  simp_rw [he]
  rw [Finset.sum_comm]

def cornerBlock (M : Mat (Fin 3×I) (Fin 3×I)) (a b : Fin 3) : Mat I I :=
  M.submatrix (fun i=>(a,i)) (fun i=>(b,i))

omit [DecidableEq I] in
theorem corner_gram_decomposition (M : Mat (Fin 3×I) (Fin 3×I)) (x : Vec (CornerCoordinates I N)) :
    layerPhase M N (cornerRack I N x).1 (cornerRack I N x).2=
      crossGram (cornerBlock M 0 1) (cornerBlock M 1 0) N (fun i=>x (0,i)) (fun i=>x (1,i))+
      crossGram (cornerBlock M 0 2) (cornerBlock M 2 0) N (fun i=>x (0,i)) (fun i=>x (2,i))+
      crossGram (cornerBlock M 1 2) (cornerBlock M 2 1) N (fun i=>x (1,i)) (fun i=>x (2,i))+
      gramPrimitive (cornerBlock M 0 0) (fun i=>x (0,i))+
      gramPrimitive (cornerBlock M 1 1) (fun i=>x (1,i))+
      gramPrimitive (cornerBlock M 2 2) (fun i=>x (2,i)) := by
  simp only [cross_gram_apply,gramPrimitive,layer_form,mpair,LinearMap.coe_mk,AddHom.coe_mk]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_three,Finset.sum_add_distrib]
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  dsimp only [cornerBlock,Matrix.submatrix,cornerRack,keyPlus,keyMinus]
  simp only [LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,Matrix.of_apply]
  abel

def cornerProduct (D : Wgt (KeyCoordinates I N)) (x : Rack (Fin 3×I) N) : ℝ :=
  let u := (rackCoordinates I N).symm (led 0 x)
  let v := (rackCoordinates I N).symm (led 1 x)
  let w := (rackCoordinates I N).symm (led 2 x)
  D u*D v*D w*D (u+v+w)

omit [Fintype I] [DecidableEq I] in
theorem corner_product_bound (D : Wgt (KeyCoordinates I N)) (hD : ∀ x,|D x|≤1)
    (x : Rack (Fin 3×I) N) : |cornerProduct D x|≤1 := by
  dsimp only [cornerProduct]
  simp only [abs_mul]
  exact (mul_le_mul (mul_le_mul (mul_le_mul (hD _) (hD _) (abs_nonneg _) (by norm_num))
    (hD _) (abs_nonneg _) (by norm_num)) (hD _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

/-- The batch hypothesis in the rank-sum theorem follows from the actual
four-corner Fourier estimate with the original ordered Gram mask. -/
theorem corner_product_fourier (E : Rail I) (Z : Vec E)
    (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1) (hs : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (M : Mat (Fin 3×I) (Fin 3×I)) (hM : ∀ a b,withinRail (cornerBlock M a b) E)
    (ξ : KeyCoordinates (Fin 3×I) N) :
    |linearFourier (fun x=>phasedBy M (rackCoordinates (Fin 3×I) N x)*
      cornerProduct D (rackCoordinates (Fin 3×I) N x)) ξ|≤δ^2+bp (-(N:ℝ)/2) := by
  let g (x : Rack (Fin 3×I) N) :=
    vectorPhase ξ ((rackCoordinates (Fin 3×I) N).symm x)*phasedBy M x*cornerProduct D x
  have he : linearFourier (fun x=>phasedBy M (rackCoordinates (Fin 3×I) N x)*
      cornerProduct D (rackCoordinates (Fin 3×I) N x)) ξ=
      avg unif (fun x : Vec (CornerCoordinates I N)=>g (cornerRack I N x)) := by
    have h1 := mapW_avg unif (rackCoordinates (Fin 3×I) N).toEquiv g
    have h2 := mapW_avg unif (cornerRack I N).toEquiv g
    rw [unif_equiv] at h1 h2
    rw [h2] at h1
    simp only [LinearEquiv.coe_toEquiv] at h1
    rw [h1]
    unfold linearFourier
    apply avg_congr
    intro x _
    simp only [g,LinearEquiv.symm_apply_apply]
    ring
  rw [he]
  have hh := gram_corner_batch_fourier E Z D δ hδ hD hs hF
    (cornerBlock M 0 1) (cornerBlock M 1 0)
    (cornerBlock M 0 2) (cornerBlock M 2 0)
    (cornerBlock M 1 2) (cornerBlock M 2 1)
    (cornerBlock M 0 0) (cornerBlock M 1 1) (cornerBlock M 2 2)
    (hM 0 1) (hM 0 0) (hM 1 1) (hM 2 2)
    (fun c : CornerCoordinates I N=>ξ (c.2.1,(c.2.2.1,(c.1,c.2.2.2))))
  convert hh using 1
  congr 1
  unfold linearFourier
  apply avg_congr
  intro x _
  dsimp only [g,phasedBy]
  rw [corner_rack_character,corner_gram_decomposition]
  dsimp only [gramCornerBatch,cornerProduct]
  have hc (a : Fin 3) : (rackCoordinates I N).symm (led a (cornerRack I N x))=(fun i=>x (a,i)) := by
    funext i
    rcases i with ⟨u,b,i⟩
    cases b <;> rfl
  simp only [hc]
  ring

/-- Complete retained-corner Gram sum, with all original mask equations and
an arbitrary joint Fourier weight. -/
theorem four_corner_gram_sum (E : Rail I) (Z : Vec E)
    (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0≤δ)
    (hD : ∀ x,|D x|≤1) (hs : ∀ x,D x≠0→traced (keyPlus x,keyMinus x) E Z)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (R : Rail (T×(Fin 3×I))) (Y : Vec R)
    (hR : ∀ v∈R,(v.1.2.2,v.2.2.2)∈E)
    (w : Wgt (KeyCoordinates (T×(Fin 3×I)) N)) (t : ℕ)
    (hroom : peakExpense T (Fin 3×I) 1≤(N:ℝ)/2) :
    |avg unif (fun x=>(∏ i:T,cornerProduct D (led i x))*
      w ((rackCoordinates (T×(Fin 3×I)) N).symm x)*ind (traced x R Y))|≤
      bp (-(R.card:ℝ))*((num (T×(Fin 3×I))+1)*
        bp (num T*num (Fin 3×I)*num (Fin 3×I))*
        (bp (peakExpense T (Fin 3×I) t)*
          ((δ^2+bp (-(N:ℝ)/2))^Fintype.card T*
            bp ((N:ℝ)*blockCompletionCost (Fin 3×I)*t))+
          bp ((peakExpense T (Fin 3×I) 1-(N:ℝ)/2)*t)))*fourierNorm w := by
  classical
  apply gram_pattern_sum (fun u v : Fin 3×I=>(u.2,v.2)∈E) R hR Y
    (fun _=>cornerProduct D) _ (add_nonneg (sq_nonneg _) (bp_pos _).le)
    (fun _=>corner_product_bound D hD) _ w t hroom
  intro M hM _ ξ
  apply corner_product_fourier E Z D δ hδ hD hs hF M _ ξ
  intro a b i j hij
  exact hM (a,i) (b,j) hij

end
end Lax793645Proofs.Simplifications
