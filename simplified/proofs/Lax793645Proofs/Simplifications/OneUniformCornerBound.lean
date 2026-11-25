import Lax793645Proofs.Simplifications.OneUniformBatchBound

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype G] [DecidableEq G] {p : Shape} {n N : ℕ}

theorem one_uniform_four_corner_bound (g : Route (I×(Fin 3×J)) G) (mixer : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N) (A : NomQuery p n g)
    (m a : ℝ) (hm : 0≤m) (hslots : ∀ i,num (Port g i)≤m)
    (hdef : ∀ i,num (Port g i)-(A i).rank≤a) (hroom : 2*m+2 ≤ N)
    (E : Rail J) (hE : ∀ i j,(i,j)∈E → (j,i)∈E) (Z : Mat J J) (hmask : ∀ v∈crowded g,(v.1.2.2,v.2.2.2)∈E)
    (D : Wgt (KeyCoordinates J N)) (δ : ℝ) (hδ : 0≤δ) (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0 → quadraticTraced E Z x)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (d t : ℕ) (hrank : peakExpense I (Fin 3×J) 1≤(N:ℝ)/2) :
    |avg (oneForumLaw mixer N) (fun x=>∏ i:I,cornerProduct D (led i (onePeek g A x)))|≤
      oneRawBatchBudget I (Fin 3×J) G N (δ^2+bp (-(N:ℝ)/2)) m a d t := by
  classical
  apply one_raw_frame_uniform_bound g mixer hN A m a hm hslots hdef hroom
    (fun u v : Fin 3×J=>(u.2,v.2)∈E) (fun u v=>hE u.2 v.2) hmask
    (fun _=>cornerProduct D) _ (add_nonneg (sq_nonneg _) (bp_pos _).le)
    (fun _=>corner_product_bound D hD) _ d t hrank
  intro M hMs hM _ ξ
  apply quadratic_corner_product_fourier E Z D δ hδ hD hs hF M hMs _ ξ
  intro a b i j hij
  exact hM (a,i) (b,j) hij

end
end Lax793645Proofs.Simplifications
