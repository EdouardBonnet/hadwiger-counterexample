import Lax793645Proofs.Simplifications.FixedGramFourCorners
import Lax793645Proofs.Simplifications.CornerPatternSum
import Lax793645Proofs.Simplifications.QuadraticGramCharacters

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}

/-- Only symmetric supported Gram characters are fixed. This is precisely
quadratic Gram information, without specifying ordered pairings. -/
def quadraticTraced (E : Rail I) (Z : Mat I I) (x : KeyCoordinates I N) : Prop:=
  ∀ M : Mat I I,Mᵀ=M → withinRail M E → gramPrimitive M x=mpair M Z

theorem quadratic_code_traced (E : Rail I) (Z : Mat I I) (x : KeyCoordinates I N)
    (hx : quadraticGramCode ((keyPlus x)ᵀ*keyMinus x)=quadraticGramCode Z) :
    quadraticTraced E Z x := by
  intro M hM _
  rw [gramPrimitive,layer_form]
  exact symmetric_pairing_quadratic_code M _ _ hM hx

theorem symmetric_corner_block (M : Mat (Fin 3×I) (Fin 3×I)) (hM : Mᵀ=M)
    (a b : Fin 3) : (cornerBlock M a b)ᵀ=cornerBlock M b a := by
  ext i j
  exact congrFun (congrFun hM (b,i)) (a,j)

/-- The local retained-column estimate for the one-frame construction.
The resonant primitive is symmetric because the original Gram character
is symmetric; it is therefore constant on the quadratic key variety. -/
theorem quadratic_corner_batch_fourier (E : Rail I) (Z : Mat I I)
    (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hD : ∀ x,|D x| ≤ 1) (hs : ∀ x,D x≠0 → quadraticTraced E Z x)
    (hF : ∀ ξ,|linearFourier D ξ| ≤ δ)
    (M : Mat (Fin 3×I) (Fin 3×I)) (hM : Mᵀ=M)
    (hm : ∀ a b,withinRail (cornerBlock M a b) E)
    (ξ : Vec (CornerCoordinates I N)) :
    |linearFourier (gramCornerBatch D
      (cornerBlock M 0 1) (cornerBlock M 1 0)
      (cornerBlock M 0 2) (cornerBlock M 2 0)
      (cornerBlock M 1 2) (cornerBlock M 2 1)
      (cornerBlock M 0 0) (cornerBlock M 1 1) (cornerBlock M 2 2)) ξ| ≤ 
      δ^2+bp (-(N:ℝ)/2) := by
  have hfix a x (hx : D x≠0) :
      gramPrimitive (cornerBlock M a a) x=mpair (cornerBlock M a a) Z :=
    hs x hx _ (symmetric_corner_block M hM a a) (hm a a)
  have hres (he : cornerBlock M 1 0=cornerBlock M 0 1) :
      ∃ c:F,∀ x,D x≠0 → gramPrimitive (cornerBlock M 0 1) x=c := by
    refine ⟨mpair (cornerBlock M 0 1) Z,fun x hx=>?_⟩
    exact hs x hx _ ((symmetric_corner_block M hM 0 1).trans he) (hm 0 1)
  unfold linearFourier
  simp_rw [triple_character]
  let F (u v w : KeyCoordinates I N) :=
    vectorPhase (fun i=>ξ (0,i)) u*vectorPhase (fun i=>ξ (1,i)) v*
    vectorPhase (fun i=>ξ (2,i)) w*(D u*D v*D w*D (u+v+w)*
      wsign (crossGram (cornerBlock M 0 1) (cornerBlock M 1 0) N u v+
        crossGram (cornerBlock M 0 2) (cornerBlock M 2 0) N u w+
        crossGram (cornerBlock M 1 2) (cornerBlock M 2 1) N v w+
        gramPrimitive (cornerBlock M 0 0) u+
        gramPrimitive (cornerBlock M 1 1) v+gramPrimitive (cornerBlock M 2 2) w))
  change |avg unif (fun x : Vec (CornerCoordinates I N)=>
    F (fun i=>x (0,i)) (fun i=>x (1,i)) (fun i=>x (2,i)))| ≤ _
  rw [triple_average (K:=Fin N×(Bool×I)) F]
  have hh:=full_fixed_gram_four_corner D δ hδ hD hF
    (cornerBlock M 0 1) (cornerBlock M 1 0)
    (cornerBlock M 0 2) (cornerBlock M 2 0)
    (cornerBlock M 1 2) (cornerBlock M 2 1)
    (cornerBlock M 0 0) (cornerBlock M 1 1) (cornerBlock M 2 2)
    hres _ _ _ (hfix 0) (hfix 1) (hfix 2)
    (fun i=>ξ (0,i)) (fun i=>ξ (1,i)) (fun i=>ξ (2,i))
  convert hh using 1
  congr 1
  apply avg_congr
  intro x _
  apply avg_congr
  intro y _
  apply avg_congr
  intro z _
  dsimp only [F]
  ring

theorem quadratic_corner_product_fourier (E : Rail I) (Z : Mat I I)
    (D : Wgt (KeyCoordinates I N)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hD : ∀ x,|D x| ≤ 1) (hs : ∀ x,D x≠0 → quadraticTraced E Z x)
    (hF : ∀ ξ,|linearFourier D ξ| ≤ δ)
    (M : Mat (Fin 3×I) (Fin 3×I)) (hM : Mᵀ=M)
    (hm : ∀ a b,withinRail (cornerBlock M a b) E)
    (ξ : KeyCoordinates (Fin 3×I) N) :
    |linearFourier (fun x=>phasedBy M (rackCoordinates (Fin 3×I) N x)*
      cornerProduct D (rackCoordinates (Fin 3×I) N x)) ξ| ≤ δ^2+bp (-(N:ℝ)/2) := by
  let g (x : Rack (Fin 3×I) N) :=
    vectorPhase ξ ((rackCoordinates (Fin 3×I) N).symm x)*phasedBy M x*cornerProduct D x
  have he : linearFourier (fun x=>phasedBy M (rackCoordinates (Fin 3×I) N x)*
      cornerProduct D (rackCoordinates (Fin 3×I) N x)) ξ=
      avg unif (fun x : Vec (CornerCoordinates I N)=>g (cornerRack I N x)) := by
    have h1:=mapW_avg unif (rackCoordinates (Fin 3×I) N).toEquiv g
    have h2:=mapW_avg unif (cornerRack I N).toEquiv g
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
  have hh:=quadratic_corner_batch_fourier E Z D δ hδ hD hs hF M hM hm
    (fun c : CornerCoordinates I N=>ξ (c.2.1,(c.2.2.1,(c.1,c.2.2.2))))
  convert hh using 1
  congr 1
  unfold linearFourier
  apply avg_congr
  intro x _
  dsimp only [g,phasedBy]
  rw [corner_rack_character,corner_gram_decomposition]
  dsimp only [gramCornerBatch,cornerProduct]
  have hc (a : Fin 3) :
      (rackCoordinates I N).symm (led a (cornerRack I N x))=(fun i=>x (a,i)) := by
    funext i
    rcases i with ⟨u,b,i⟩
    cases b <;> rfl
  simp only [hc]
  ring

end
end Lax793645Proofs.Simplifications
