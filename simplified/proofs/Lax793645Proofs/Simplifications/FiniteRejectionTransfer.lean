/-
The finite projection argument with an extra rejected-input event.
The projection partition and comparisons refer to the original densities;
only a truncated overlap is transferred to the accepted densities.
The clipping proof is adapted from ProjectedSurrogates (OpenAI,
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0).
-/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProjectedSurrogates
import Lax793645Proofs.Simplifications.GoodInputStability

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
noncomputable section
variable {A B : Type} [Fintype A] [Fintype B]

private theorem cost_gap (u : Wgt A) (p : A→B) (f g : Wgt A) (h : ∀ i,g i≤ f i)
    (hu : IsLaw u) :
    lcost u (banner u p f) (banner u p g)=lcost u f g := by
  have hf (i : A) : |banner u p f i-banner u p g i|=banner u p f i-banner u p g i :=
    abs_of_nonneg (sub_nonneg.mpr (book_order u p hu g f h _))
  have hg (f : Wgt A) : avg u f = avg u (banner u p f) := by
    have hh := cash_orth u hu.nz p f (fun _=>1); simpa only [dip,Function.comp_apply,mul_one] using hh.symm
  unfold lcost; simp_rw [hf, abs_of_nonneg (sub_nonneg.mpr (h _)), avg_sub]
  rw [← hg f, ← hg g]

set_option maxHeartbeats 800000 in
theorem density_mend_clipped_implementation (u : Wgt A) (hu : IsLaw u) (p : A→B) (R : ℝ) (hR : 0≤ R)
    (f g x y : Wgt A) (hf : bower f) (hg : bower g) (hx : SubLaw x)
    (hy : SubLaw y) (h1 : lsupp x u) (h2 : lsupp y u) :
    let V f g := varOne (mapW (fun i=>u i*f i) p) (mapW g p)+trayLoss R u g
    dip u f g ^ 2 ≤ dip u (mcut R u x) (mcut R u y) + |rebate u (mcut R u x) (mcut R u y) p|+
      (V f x+V g y) := by
  classical
  intro V
  let F:=banner u p f; let G:=banner u p g
  let X:=banner u p (mcut R u x); let Y:=banner u p (mcut R u y)
  have he (f x : Wgt A) (hx : SubLaw x) (h : lsupp x u) :
      lcost u (banner u p f) (banner u p (mcut R u x)) ≤ V f x := by
    let F := banner u p f; let X:=banner u p (density u x); let Z:=banner u p (mcut R u x)
    obtain ⟨h1,h2⟩:=density_trim u x hx.nz hu R hR
    have hh : lcost u F Z≤lcost u F X+lcost u X Z := by
      unfold lcost; rw [← avg_add]; exact avg_mono hu.nz fun i=>abs_sub_le _ _ _
    exact hh.trans (add_le_add (density_error u p hu f x h)
      (le_trans (cost_gap u p (density u x) _ h1 hu).le h2))
  have hh i : F i*G i ≤ X i*Y i + (|F i-X i|+|G i-Y i|) := by
    have hA := (garden u f p hu hf).2 i; have hB := (garden u g p hu hg).2 i
    have ht : 0≤X i := book_nonneg u p hu _ (fun i=> (mcut_range _ _ _ hR i).1) _
    have hq : 0≤Y i := book_nonneg u p hu _ (fun i=> (mcut_range _ _ _ hR i).1) _
    have hp := (garden u f p hu hf).1 i
    by_cases h : X i≤F i
    · by_cases h' : Y i≤ G i
      · nlinarith only [ht,hq,h,h',hA,hB, le_abs_self (F i-X i),le_abs_self (G i-Y i)]
      have hz := le_of_not_ge h'
      nlinarith only [h,hB,hz,le_abs_self (F i-X i),abs_nonneg (G i-Y i),ht]
    have hz := le_of_not_ge h
    by_cases h' : Y i≤ G i
    · nlinarith only [hA,hq,h',hz,abs_nonneg (F i-X i),le_abs_self (G i-Y i)]
    have hi := le_of_not_ge h'
    nlinarith only [hz,hq,hi,hp,abs_nonneg (F i-X i), abs_nonneg (G i-Y i)]
  let A:= mcut R u x; let B:=mcut R u y
  have h :
      dip u X Y≤dip u A B + |rebate u A B p| := by
    have h : dip u X Y-dip u A B ≤|dip u A B-dip u X Y| := by rw [abs_sub_comm]; exact le_abs_self _
    change _≤ _+ |dip u A B - dip u X Y|; linarith only [h]
  have hp := avg_mono hu.nz hh
  rw [avg_add,avg_add] at hp
  exact (le_trans (projected_min u p hu f g hf hg) hp).trans
    (add_le_add h (add_le_add (he f x hx h1) (he g y hy h2)))

theorem density_mend_clipped (u : Wgt A) (hu : IsLaw u) (p : A→B) (R : ℝ) (hR : 0≤ R)
    (f g x y : Wgt A) (hf : bower f) (hg : bower g) (hx : SubLaw x)
    (hy : SubLaw y) (h1 : lsupp x u) (h2 : lsupp y u) :
    let V f g := varOne (mapW (fun i=>u i*f i) p) (mapW g p)+trayLoss R u g
    dip u f g ^ 2 ≤ dip u (mcut R u x) (mcut R u y) + |rebate u (mcut R u x) (mcut R u y) p|+
      (V f x+V g y) := by
  intro V
  exact Lax793645.OverlapTransfer.clipped_transfer u ⟨hu.nz,hu.total⟩ p R hR
    f g x y hf hg ⟨hx.nz,hx.total⟩ ⟨hy.nz,hy.total⟩ h1 h2

theorem rejected_density_loss (u x xg : Wgt A)
    (hu : ∀ i,0 ≤ u i) (hxg : ∀ i,xg i ≤ x i) :
    avg u (fun i => density u x i-density u xg i) ≤ varOne x xg := by
  unfold avg varOne
  apply Finset.sum_le_sum
  intro i _
  rw [abs_of_nonneg (sub_nonneg.mpr (hxg i))]
  by_cases hz : u i=0
  · rw [hz,zero_mul]
    exact sub_nonneg.mpr (hxg i)
  unfold density
  exact le_of_eq (by field_simp)

theorem mcut_eq_min_of_nonneg (u x : Wgt A)
    (hu : ∀ i,0 ≤ u i) (hx : ∀ i,0 ≤ x i) (R : ℝ) :
    mcut R u x=fun i => min (density u x i) R := by
  funext i
  exact congrArg (fun z => min z R) (max_eq_left (div_nonneg (hx i) (hu i)))

set_option maxHeartbeats 800000 in
/-- Keep the original finite partitions, tail estimates and tuple-cell
comparisons. Rejection adds only R times the two deleted masses. -/
theorem density_mend_after_rejection (u : Wgt A) (hu : IsLaw u) (p : A → B)
    (R : ℝ) (hR : 0 ≤ R) (f g x y xg yg : Wgt A)
    (hf : bower f) (hg : bower g) (hx : SubLaw x) (hy : SubLaw y)
    (h1 : lsupp x u) (h2 : lsupp y u)
    (hX : ∀ i,0 ≤ xg i ∧ xg i ≤ x i) (hY : ∀ i,0 ≤ yg i ∧ yg i ≤ y i)
    (δA δB : ℝ) (hδA : varOne x xg ≤ δA) (hδB : varOne y yg ≤ δB) :
    let V f g := varOne (mapW (fun i => u i*f i) p) (mapW g p)+trayLoss R u g
    dip u f g^2 ≤ overlap u xg yg+|rebate u (mcut R u x) (mcut R u y) p|+
      (V f x+V g y)+R*(δA+δB) := by
  intro V
  have hbase := density_mend_clipped u hu p R hR f g x y hf hg hx hy h1 h2
  have hAx (i) : 0 ≤ density u xg i ∧ density u xg i ≤ density u x i :=
    ⟨div_nonneg (hX i).1 (hu.nz i),div_le_div_of_nonneg_right (hX i).2 (hu.nz i)⟩
  have hBy (i) : 0 ≤ density u yg i ∧ density u yg i ≤ density u y i :=
    ⟨div_nonneg (hY i).1 (hu.nz i),div_le_div_of_nonneg_right (hY i).2 (hu.nz i)⟩
  have hclip : dip u (mcut R u x) (mcut R u y)-R*(δA+δB) ≤
      dip u (mcut R u xg) (mcut R u yg) := by
    simpa only [dip,mcut_eq_min_of_nonneg u x hu.nz hx.nz R,
      mcut_eq_min_of_nonneg u y hu.nz hy.nz R,
      mcut_eq_min_of_nonneg u xg hu.nz (fun i => (hX i).1) R,
      mcut_eq_min_of_nonneg u yg hu.nz (fun i => (hY i).1) R] using
      good_input_truncated_overlap u (density u x) (density u y)
        (density u xg) (density u yg) R δA δB hu.nz hR hAx hBy
        ((rejected_density_loss u x xg hu.nz (fun i => (hX i).2)).trans hδA)
        ((rejected_density_loss u y yg hu.nz (fun i => (hY i).2)).trans hδB)
  have hgood : dip u (mcut R u xg) (mcut R u yg) ≤ overlap u xg yg := by
    apply avg_mono hu.nz
    intro i
    rw [mcut_eq_min_of_nonneg u xg hu.nz (fun i => (hX i).1) R,
      mcut_eq_min_of_nonneg u yg hu.nz (fun i => (hY i).1) R]
    exact mul_le_mul (min_le_left ..) (min_le_left ..)
      (le_min (hBy i).1 hR) (hAx i).1
  linarith only [hbase,hclip,hgood]

end
end Lax793645Proofs.Simplifications
