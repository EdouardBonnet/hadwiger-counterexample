import Lax793645Proofs.Simplifications.OneCoverRecords
import Lax793645Proofs.Simplifications.OneLeafMixtures
import Lax793645Proofs.Simplifications.ImageLeafRepartition

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

set_option maxHeartbeats 900000 in
theorem one_refine_labels {J : Type} [Fintype J] (P : OneUnit p n N→Prop)
    {w μ : Wgt (OneUnit p n N)}
    (label : OneUnit p n N → J)
    (hw : ∀ x,0≤w x) {D ζ u : ℝ} (hz : 0 < ζ) (hz' : ζ<1) {K K' : ℕ}
    (hn : 0<N)
    (hμ : ∀ a : ImagePin (Comp p.g) (OneColumn p n) (2*N),(onePinClosure p n).close a.sp=a.sp → pr μ (imagePinAgree oneCoordinateImages a) ≤ fee (2*N) ((ζ/6)/4) (imagePlanRank a.sp))
    {F : Tiles (OneUnit p n N)} (hT : apart F) (g : Finset (OneUnit p n N) → ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (h : ∀ i∈F,ImageRipe oneCoordinateImages (onePinClosure p n) w μ i (g i) D ζ K)
    (hk : D+u+ζ≤((ζ/6)-(ζ/6)/4)*K')
    (hu : num J ≤ bp ((u-1)*(2*N))) :
    ∃ V : Tiles (OneUnit p n N),apart V ∧
    (∀ S∈V,∃ i∈F,S⊆i ∧ (∀ x∈ S,P x) ∧
      ∃ b : ImagePin (Comp p.g) (OneColumn p n) (2*N),ImageRipe oneCoordinateImages (onePinClosure p n) w μ S b (D+u+K'+1) ζ (K+K') ∧ ((g i).sp≤b.sp ∧ ∀ x∈S,∀ y∈S,label x=label y)) ∧
    pr w (fun x => inTiles F x ∧ P x ∧ ¬inTiles V x) ≤
      allMass w F*(bp (-(2*N:ℝ))+bp (-ζ*(2*N))) := by
  classical
  refine improve F w hw P
    (fun i S => (∀ x∈ S,P x) ∧ ∃ b : ImagePin (Comp p.g) (OneColumn p n) (2*N),ImageRipe oneCoordinateImages (onePinClosure p n) w μ S b (D+u+K'+1) ζ (K+K') ∧
      ((g i).sp≤b.sp ∧ ∀ x∈S,∀ y∈S,label x=label y))
    hT (fun i hi => ?_)
  let S := i.filter P
  let Q (G : Finset (OneUnit p n N)) (b : ImagePin (Comp p.g) (OneColumn p n) (2*N)) :=
    (g i).sp≤b.sp ∧ ∀ x∈G,∀ y∈G,label x=label y
  have hs (x : OneUnit p n N) : x∈S↔ x∈i∧ P x := Finset.mem_filter
  have hq := h i hi
  let w' := partW w i
  have hw' : IsLaw w' := on_law hw hq.pos
  obtain ⟨V,hV,hX,hZ⟩ := image_repartition oneCoordinateImages (by decide : 1≤6) (onePinClosure p n) w' μ hw' S D ζ u (by omega : 0<2*N) hz hz' hμ hq.density
    label K K' Q
    (fun v=>⟨g i,fun x hx _=>hq.fixpin x ((hs x).mp hx).1,hq.closed,hq.bound,
      fun _ _ _ hG hle=>⟨hle,fun x hx y hy=>((hG x hx).2).trans ((hG y hy).2).symm⟩⟩) hk
  refine ⟨V,hV,fun x hx => ?_,?_⟩
  · obtain ⟨hS,b,hB,hL⟩ := hX x hx
    have hx' : x⊆i := hS.trans (Finset.filter_subset ..)
    obtain ⟨he,hLaw⟩ := issued_law w hw hq.pos hx' hB.pos
    refine ⟨hx', (fun z hz => ((hs ..).mp (hS hz)).2),b,⟨he,hB.fixpin,hB.closed,hB.bound,?_,?_⟩,hL⟩
    · rw [hLaw]; exact hB.clear
    rw [hLaw]; exact hB.density
  simp_rw [hs,and_assoc] at hZ
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hZ
  refine hZ.trans (add_le_add_left ?_ _)
  refine (mul_le_mul_of_nonneg_right hu (bp_pos _).le).trans ?_
  rw [←bp_add]; apply bp_le
  linarith only []

end
end Lax793645Proofs.Simplifications
