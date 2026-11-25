import Lax793645Proofs.Simplifications.OneLeafWeaving

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {w μ : Wgt (OneUnit p n N)} {D ζ : ℝ} {K : ℕ}

set_option maxHeartbeats 800000 in
theorem one_refine_leaf_labels {J : Type} [Fintype J] {s : OneLeafMixture p n N} (h : s.strength oneCoordinateImages (onePinClosure p n) w μ D ζ K) (hz : 0<ζ)
    (hw : IsLaw w) (P : OneUnit p n N→Prop)
    {u : ℝ} {K' : ℕ}
    (label : OneUnit p n N→J)
    (hz' : ζ<1) (hn : 0<N)
    (hμ : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),(onePinClosure p n).close a.sp=a.sp → pr μ (imagePinAgree oneCoordinateImages a) ≤ fee (2*N) ((ζ/6)/4) (imagePlanRank a.sp))
    (hk : D+u+ζ≤((ζ/6)-(ζ/6)/4)*K')
    (hu : num J≤bp ((u-1)*(2*N))) :
    ∃ t : OneLeafMixture p n N, t.strength oneCoordinateImages (onePinClosure p n) w μ (D+u+K'+1) ζ (K+K') ∧
      ImageLeafMixture.elder s t P (fun i j => (s.pin j).sp≤(t.pin i).sp ∧ ∀ x∈i,∀ y∈i,label x=label y) ∧
      pr w (fun x=>inTiles s.T x∧P x∧¬inTiles t.T x)≤ bp (-(2*N:ℝ))+bp (-ζ*(2*N)) := by
  classical
  obtain ⟨V,hV,hX,hF⟩:= one_refine_labels P label hw.nz hz hz' hn hμ h.part _ h.leaf hk hu
  let R (i j : Finset (OneUnit p n N)) b := j∈s.T ∧ i⊆j ∧ (∀ x∈i,P x) ∧
    ImageRipe oneCoordinateImages (onePinClosure p n) w μ i b (D+u+K'+1) ζ (K+K') ∧ ((s.pin j).sp≤b.sp ∧ ∀ x∈i,∀ y∈i,label x=label y)
  choose f h1 using (show ∀ i: Finset (OneUnit p n N),∃ b,i∈V → ∃ j,R i j b from
    fun i=>by
      by_cases hi : i∈ V
      · obtain ⟨j,hj,hp,hc,b,h⟩:= hX i hi
        exact ⟨b,fun _ => ⟨_,hj,hp,hc,h⟩⟩
      exact ⟨imageDustPin,fun hh=> (hi hh).elim⟩)
  refine ⟨⟨V,f⟩,⟨hV,fun i hi=>?_⟩,fun i hi=>?_,hF.trans (by
    have hh : allMass w s.T ≤1 := (pr_le_tot hw.nz).trans hw.total.le
    exact (mul_le_mul_of_nonneg_right hh (add_nonneg (bp_pos _).le (bp_pos _).le)).trans_eq
      (one_mul _))⟩
  · obtain ⟨_,_,_,_,hh,_⟩:= h1 i hi; exact hh
  obtain ⟨_,h',hx,hy,_,hh⟩:= h1 i hi; exact ⟨_,h',hx,hy,hh⟩

end
end Lax793645Proofs.Simplifications
