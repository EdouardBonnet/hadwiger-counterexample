import Lax793645Proofs.Simplifications.UniformRawBatchBound

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype G] [DecidableEq G] {p : Shape} {n N : ℕ}

theorem uniform_four_corner_bound (g : Route (I×(Fin 3×J)) G) (mixer : Mixer p n)
    (hN : 2*num (Full p n)<N) (A : NomQuery p n g)
    (m a : ℝ) (hm : 0≤m) (hslots : ∀ i,num (Port g i)≤m)
    (hdef : ∀ i,num (Port g i)-(A i).rank≤a) (hroom : 2*m-(N:ℝ)≤-1)
    (E : Rail J) (Z : Vec E) (hmask : ∀ v∈crowded g,(v.1.2.2,v.2.2.2)∈E)
    (D : Wgt (KeyCoordinates J N)) (δ : ℝ) (hδ : 0≤δ) (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0 → traced (keyPlus x,keyMinus x) E Z)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (d t : ℕ) (hrank : peakExpense I (Fin 3×J) 1≤(N:ℝ)/2) :
    |avg (forumLaw mixer N) (fun x=>∏ i:I,cornerProduct D (led i (peekR p g A A x)))|≤
      rawBatchBudget I (Fin 3×J) G N (δ^2+bp (-(N:ℝ)/2)) m a d t := by
  classical
  apply raw_frame_uniform_bound g mixer hN A m a hm hslots hdef hroom
    (fun u v : Fin 3×J=>(u.2,v.2)∈E) hmask
    (fun _=>cornerProduct D) _ (add_nonneg (sq_nonneg _) (bp_pos _).le)
    (fun _=>corner_product_bound D hD) _ d t hrank
  intro M hM _ ξ
  apply corner_product_fourier E Z D δ hδ hD hs hF M _ ξ
  intro a b i j hij
  exact hM (a,i) (b,j) hij

end
end Lax793645Proofs.Simplifications
