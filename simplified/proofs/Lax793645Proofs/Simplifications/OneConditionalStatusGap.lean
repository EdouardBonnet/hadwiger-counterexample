import Lax793645Proofs.Simplifications.OneStatusCoordinates
import Lax793645Proofs.Simplifications.AffineConditionalSupports

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis LinearMap Function Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N d : ℕ}

theorem one_status_coordinates_bounded (hg : Odd p.g) (i : Nodes) (v : Ax p n d)
    (m : Mixer p n) (o : OneUnit p n N) (l : Tag p.g) (s : Label p.b)
    (f : Flavor p.g) (K : ℕ) (hd : d≤K^2)
    (hv : ∀ j : Fin d,totalRank (v (Pi.single j 1))≤K) :
    HasLinearCells (fun (_ : Unit) x=>oneSpecify p i v m o l s f x)
      (oneStatusCoordinateBound p (K^2) K) := by
  apply linear_cells_mono (one_status_coordinates hg i v m o l s f K hv)
  unfold oneStatusCoordinateBound
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _) _

variable {C : Type} [AddCommGroup C] [Module F C] [Fintype C]

/-- Exact full-status probabilities on a linear key cell, conditioned
on the diagonal value recorded in that status. These are defined before
the protected-base rejection. -/
def oneConditionalStatus (L : Knobs p.g n→ₗ[F]C) (k : C)
    (i : Nodes) (v : Ax p n d) (m : Mixer p n) (o : OneUnit p n N)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g) (z : Magazine p d) (c : C) :=
  pr (onW (unifOn (fun x=>L x+k=c)) (fun x=>dialed p l f x=z.1.sumBit))
    (fun x=>oneSpecify p i v m o l s f x=z)

/-- The construction's actual statuses have a uniform positive overlap
gap. The bound is independent of the number of common key rows. -/
theorem one_conditional_status_gap {d' : ℕ}
    (hg : Odd p.g) (K : ℕ) (hd : d≤K^2) (hd' : d'≤K^2)
    (L L' : Knobs p.g n→ₗ[F]C) (k k' : C)
    (S S' : C→ₗ[F]Knobs p.g n)
    (hS : ∀ c,L (S c)=c) (hS' : ∀ c,L' (S' c)=c)
    (i i' : Nodes) (v : Ax p n d) (v' : Ax p n d')
    (hv : ∀ j : Fin d,totalRank (v (Pi.single j 1))≤K)
    (hv' : ∀ j : Fin d',totalRank (v' (Pi.single j 1))≤K)
    (m : Mixer p n) (o o' : OneUnit p n N)
    (l : Tag p.g) (s s' : Label p.b) (f f' : Flavor p.g)
    (z : Magazine p d) (z' : Magazine p d')
    (ν : Wgt C) (hν : ∀ c,unif c/2≤ν c) :
    let overlap:=avg ν (fun c=>
      oneConditionalStatus L k i v m o l s f z c*
      oneConditionalStatus L' k' i' v' m o' l s' f' z' c)
    overlap=0 ∨ bp (-(4*(oneStatusCoordinateBound p (K^2) K:ℝ)+1))≤overlap := by
  have hf:=one_status_coordinates_bounded hg i v m o l s f K hd hv
  have hf':=one_status_coordinates_bounded hg i' v' m o' l s' f' K hd' hv'
  exact affine_scoped_overlap_gap L L' k k' S S' hS hS'
    (oneSpecify p i v m o l s f) (oneSpecify p i' v' m o' l s' f')
    (oneStatusCoordinateBound p (K^2) K) hf hf'
    (fun z:Magazine p d=>z.1.sumBit) (fun z:Magazine p d'=>z.1.sumBit) z z' ν hν

end
end Lax793645Proofs.Simplifications
