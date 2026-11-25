import Lax793645Proofs.Simplifications.QuadraticNormalizedBatches
import Lax793645Proofs.Simplifications.OneNominalFactors

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype G] [DecidableEq G] {p : Shape} {n N : ℕ}

/-- Explicit conditional bound for the actual raw frame distribution,
with arbitrary nominal dependencies and every original batch retained. -/
theorem one_raw_frame_bound (g : Route (I×J) G) (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N) (A : NomQuery p n g)
    (hroom : ∀ i,2*((A i).rank:ℝ)+2 ≤ N)
    (P : J→J→Prop) [DecidableRel P] (hP : ∀ u v,P u v → P v u) (hmask : ∀ v∈crowded g,P v.1.2 v.2.2)
    (f : I→Wgt (Rack J N)) (ε : ℝ) (hε : 0≤ε) (hb : ∀ i x,|f i x|≤1)
    (hf : ∀ (M : Mat J J),Mᵀ=M → (∀ u v,¬P u v→M u v=0)→∀ i ξ,
      |linearFourier (fun x=>phasedBy M (rackCoordinates J N x)*f i (rackCoordinates J N x)) ξ|≤ε)
    (d t : ℕ) (hrank : peakExpense I J 1≤(N:ℝ)/2)
    (B : ℝ) (hB : 1≤B)
    (hc : ∀ i,singleKernelSieveCost (Fin (A i).rank) d≤B) :
    |avg (oneForumLaw m N) (fun x=>∏ i,f i (led i (onePeek g A x)))|≤
      (8:ℝ)^Fintype.card G*
        ((4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*∑ i,(num (Port g i)-(A i).rank))*
          quadraticPatternBudget I J N ε t*(∏ i,singleKernelSieveCost (Fin (A i).rank) d)+
         B^Fintype.card G*∑ i,16*(d+2)*bp ((((A i).rank:ℝ)+2)*d+
           ((d:ℝ)+1)*(4*((A i).rank:ℝ)-(N:ℝ)))) := by
  obtain ⟨L,Q,hL,himage⟩:=one_raw_network_factored g m hN A
  have he:=mapW_avg (oneForumLaw m N) (onePeek g A) (fun x=>∏ i,f i (led i x))
  rw [himage] at he
  rw [←he]
  have hh:=quadratic_dependent_batch_bound g P hP hmask L Q hL
    (fun i=>by simpa only [num,Fintype.card_fin] using hroom i)
    f ε hε hb hf d t hrank B hB hc
  simpa only [num,Fintype.card_fin] using hh

/-- Direct specialization to four copies of a single Fourier-small key
test. Nominal dependencies are unrestricted in this raw-frame statement. -/
theorem one_raw_four_corner_bound (g : Route (I×(Fin 3×J)) G) (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3 ≤ N) (A : NomQuery p n g)
    (hroom : ∀ i,2*((A i).rank:ℝ)+2 ≤ N)
    (E : Rail J) (hE : ∀ i j,(i,j)∈E → (j,i)∈E) (Z : Mat J J) (hmask : ∀ v∈crowded g,(v.1.2.2,v.2.2.2)∈E)
    (D : Wgt (KeyCoordinates J N)) (δ : ℝ) (hδ : 0≤δ) (hD : ∀ x,|D x|≤1)
    (hs : ∀ x,D x≠0→quadraticTraced E Z x)
    (hF : ∀ ξ,|linearFourier D ξ|≤δ)
    (d t : ℕ) (hrank : peakExpense I (Fin 3×J) 1≤(N:ℝ)/2)
    (B : ℝ) (hB : 1≤B)
    (hc : ∀ i,singleKernelSieveCost (Fin (A i).rank) d≤B) :
    |avg (oneForumLaw m N) (fun x=>∏ i:I,cornerProduct D (led i (onePeek g A x)))|≤
      (8:ℝ)^Fintype.card G*
        ((4:ℝ)^Fintype.card G*bp (2*(N:ℝ)*∑ i,(num (Port g i)-(A i).rank))*
          quadraticPatternBudget I (Fin 3×J) N (δ^2+bp (-(N:ℝ)/2)) t*
          (∏ i,singleKernelSieveCost (Fin (A i).rank) d)+
         B^Fintype.card G*∑ i,16*(d+2)*bp ((((A i).rank:ℝ)+2)*d+
           ((d:ℝ)+1)*(4*((A i).rank:ℝ)-(N:ℝ)))) := by
  classical
  apply one_raw_frame_bound g m hN A hroom (fun u v : Fin 3×J=>(u.2,v.2)∈E) (fun u v=>hE u.2 v.2) hmask
    (fun _=>cornerProduct D) _ (add_nonneg (sq_nonneg _) (bp_pos _).le)
    (fun _=>corner_product_bound D hD) _ d t hrank B hB hc
  intro M hsM hM _ ξ
  apply quadratic_corner_product_fourier E Z D δ hδ hD hs hF M hsM _ ξ
  intro a b i j hij
  exact hM (a,i) (b,j) hij

end
end Lax793645Proofs.Simplifications
