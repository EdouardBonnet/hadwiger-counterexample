import Lax793645Proofs.Simplifications.ProtectedBaseSampling
import Lax793645Proofs.Simplifications.AffineSelectorExclusions
import Lax793645Proofs.Simplifications.GoodInputStability

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def selectorProtectionDim (p : Shape) (q K : ℕ) := q*(Fintype.card (Bool × Place p)*K)
def baseProtectionDim (p : Shape) (K : ℕ) :=
  Fintype.card (SelIdx p.b p.j)*(Fintype.card (Bool × Place p)*K)

/-- Deterministic template admissibility. Base independence is checked on
the sampled inputs, with a uniform rejection bound below. -/
def affinePenSpace (v : Template p I) (a : Plan p n) (q K : ℕ) : Prop :=
  ∃ (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n))),
    dim U ≤ selectorProtectionDim p q K ∧ dim V ≤ baseProtectionDim p K ∧
    (∀ i z,sPin a z i ≤ tensorCross U V) ∧
    (∀ i z x,x ∈ sPin a z i → Matrix.rank (flattenMatrix.symm x) ≤ q →
      x ∈ tensorRectangle U V) ∧
    LinearIndependent F (U.mkQ ∘ (fun j => selV p.j (v.s j)))

theorem template_affine_avoids (v : Template p I) (a : Plan p n) (q : ℕ)
    (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n)))
    (hpin : ∀ i z,sPin a z i ≤ tensorCross U V)
    (hlow : ∀ i z x,x ∈ sPin a z i → Matrix.rank (flattenMatrix.symm x) ≤ q →
      x ∈ tensorRectangle U V)
    (hs : LinearIndependent F (U.mkQ ∘ (fun j => selV p.j (v.s j))))
    (x : Inputs p n I)
    (hb : LinearIndependent F (V.mkQ ∘ (fun j => baseV ((v.draw x).par j)))) :
    affineAvoids (v.draw x) a q := by
  intro i
  exact ⟨U,V,hpin i,hlow i,
    hs.comp (fun j : CallsAt (v.draw x) i => j.val) Subtype.val_injective,
    hb.comp (fun j : CallsAt (v.draw x) i => j.val) Subtype.val_injective⟩

/-- Concrete rejection cost for the realization theorem's actual hypothesis.
It is uniform in every orientation and any subsequent acceptance weights. -/
theorem affine_query_rejection (v : Template p I) (a : Plan p n) (q K : ℕ)
    (hpen : affinePenSpace v a q K) (z : I → F)
    (hz : ∀ i,IsLaw (scopedBit p n (v.t i) (v.f i) (z i))) :
    pr (v.state z n) (fun x => ¬affineAvoids (v.draw x) a q) ≤
      bp (num I+(baseProtectionDim p K:ℝ)-(n:ℝ)) := by
  obtain ⟨U,V,_,hV,hpin,hlow,hs⟩ := hpen
  have hsub := pr_mono (prodW_law hz).nz (fun x
    (hx : ¬affineAvoids (v.draw x) a q) hb =>
      hx (template_affine_avoids v a q U V hpin hlow hs x hb))
  apply hsub.trans ((template_base_rejection v z hz V).trans (bp_le ?_))
  have hdim : (dim V:ℝ) ≤ baseProtectionDim p K := by exact_mod_cast hV
  linarith

theorem affine_query_test_stability (v : Template p I) (a : Plan p n) (q K : ℕ)
    (hpen : affinePenSpace v a q K) (z : I → F)
    (hz : ∀ i,IsLaw (scopedBit p n (v.t i) (v.f i) (z i)))
    (accept f : Wgt (Inputs p n I)) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x,0 ≤ accept x ∧ accept x ≤ 1) (hf : ∀ x,|f x| ≤ C) :
    |avg (v.state z n) (fun x => accept x*f x)-
      avg (v.state z n) (fun x => accept x*ind (affineAvoids (v.draw x) a q)*f x)| ≤
        C*bp (num I+(baseProtectionDim p K:ℝ)-(n:ℝ)) :=
  good_input_bounded_test _ _ _ _ _ _ (prodW_law hz).nz ha hC hf
    (affine_query_rejection v a q K hpen z hz)

end
end Lax793645Proofs.Simplifications
