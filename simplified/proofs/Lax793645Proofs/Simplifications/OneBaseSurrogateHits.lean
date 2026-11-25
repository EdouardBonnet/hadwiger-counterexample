import Lax793645Proofs.Simplifications.OneBaseQueries
import Lax793645Proofs.Simplifications.OneLinearComparisonCalendar

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneAppearance Template Filter Finset Matrix Function
open scoped BigOperators Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OneQuill
variable {p:Shape} {q:Format} {d:Rates} {b:Bool} {n N K r:ℕ}
variable (w:Quill p q d b) (t:Tagging p (Messenger q)) (z:Messenger q→F)

theorem one_tiny_cell_loss (Y:OneSilhouette p N r) {δ:ℝ} (hd:0≤δ) (i : Messenger q)
    (hN: 2*num (Messenger q×Toast p)+2≤(N:ℝ))
    (hh:2*num (Toast p)-(N:ℝ)≤ -1) :
    let x:= w.allure t z i
    let μ:=oneLawNu p N t z
    pr μ (fun y=> oneReference x Y (Y (t i) (z i) (y i)) < δ) ≤
      r*δ+2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2) := by
  classical
  intro a μ
  let I:=Messenger q
  let Ω:=fun i=> oneLawOmega p N (t i) (z i)
  let S:=fun y=>oneReference a Y (Y (t i) (z i) y)<δ
  let f : ∀ i:Messenger q,Wgt (OneAtomKey (p:=p) (t i) N) := fun j=>
    if h:j=i then h ▸ (fun x : OneAtomKey (p:=p) (t i) N=> ind (S x)) else fun _=>1
  have hi : f i=fun x=>ind (S x) := by unfold f; simp
  have hf j (h:j≠i) : f j=fun _ => 1 := by unfold f; simp [h]
  have hg j x : |f j x| ≤ 1 := by
    by_cases h:j=i
    · subst j; rw [hi]; exact (abs_of_nonneg (ind_nonneg _)).le.trans (ind_le_one _)
    rw [hf j h]; simp
  have he x : prodW f x= ind (S (x i)) := by
    unfold prodW; rw [Finset.prod_eq_single i _ (by simp),hi]
    intro b _ hb; rw [hf _ hb]
  have hR :
      ∏ i,avg (Ω i) (f i) = pr (Ω i) S := by
    rw [Finset.prod_eq_single i _ (by simp),hi]; rfl
    intro b _ hb; rw [hf _ hb,(one_omega_law _ _ hh).avg_const]
  let L:=2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2)
  have hM : pr μ (fun x=> S (x i)) ≤ pr (Ω i) S+L := by
    have hm := one_reference_product t z f hg hN
    change |avg μ (prodW f)-∏ i,avg (Ω i) (f i)|≤L at hm
    rw [show prodW f=(fun x=>ind (S (x i))) from funext he,hR] at hm
    exact sub_le_iff_le_add'.mp ((abs_le.mp hm).2)
  have hZ : pr (Ω i) S ≤ r*δ := by
    let Q:=fun x=> oneReference a Y x < δ
    rw [show pr (Ω i) S= pr (oneReference a Y) Q from (mapW_pr (Ω i) (Y (t i) (z i)) Q).symm]
    exact haze_small _ δ hd
  exact hM.trans (add_le_add hZ le_rfl)

set_option maxHeartbeats 1000000 in
theorem one_base_sheen_hit (m:Mixer p n) (Y:OneSilhouette p N r) (o:OneUnit p n N) (s:Charts p n d)
    (H:OneKeys t N→Prop)
    {ε δ:ℝ} (hp:0<δ) (he: ε≤pr (oneLawNu p N t z) H)
    (hw : w.moral t z) (ht :1≤p.r) (hn:2*p.r≤n)
    (hg : OneBaseSteady w m K s o)
    (hN:2*num (Messenger q×Toast p)+2≤(N:ℝ)) (hh:2*num (Toast p)-(N:ℝ)≤ -1)
    (hK : num (Messenger q)*(r*δ+2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2)) ≤ ε/2)
    (hq:oneGenericGauze p δ δ Y m K o) :
    oneDilate w t K * (ε/2) ≤ oneBaseSheen w t z o m s Y (fun x=> ind (H x)) := by
  classical
  let ν:=oneLawNu p N t z
  have hu i:IsLaw (w.policies t z n i) := Appearance.witLaw (w.allure_apt t z hw _) ht hn
  have hν := one_nu_law t z hN
  let I:=Messenger q
  let f i:=w.allure t z i
  let P (i:I) (x:OneKeys t N) := δ≤ oneReference (f i) Y (Y (t i) (z i) (x i))
  let Q (x:OneKeys t N):=∀ i,P i x
  have hm i : pr ν (fun x=>¬P i x)≤
      r*δ+2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2) := by
    unfold P; simp_rw [not_le]
    exact one_tiny_cell_loss w t z Y hp.le _ hN hh
  have h1 : pr ν (fun x=>¬Q x) ≤ ε/2 := by
    have hx (x) (h:¬Q x) : ∃ i,¬ P i x := Classical.not_forall.mp h
    refine ((pr_mono hν.nz hx).trans (pr_exists_le hν.nz _)).trans
      ((Finset.sum_le_sum (fun i _=>hm i)).trans ?_)
    rw [Finset.sum_const]
    simpa only [Finset.card_univ,nsmul_eq_mul] using hK
  have h2 : ε/2 ≤ pr ν (fun x=> H x∧Q x) :=
    le_trans (by linarith only [he,h1]) (pr_shield hν.nz H Q)
  let L:=oneDilate w t K; let Z:=basebeta p K/2
  have hh x (hx:Q x) : L ≤ oneBaseMirror w t z o m s Y x := by
    have hg' i : Z ≤ oneBaseSeraph w t z o m s Y i (x i):= one_base_thin_glaze w t z m Y o i s (x i) hp hw hg hq ht hn (hx i)
    apply mul_le_mul_of_nonneg_left _ (one_kappa_pos _).le
    change Z^Fintype.card I≤prodW _ _
    rw [show Z^Fintype.card I=∏ i:Messenger q,Z from by simp [I]]
    exact Finset.prod_le_prod (fun i _=> (half_pos (basebeta_pos _ _)).le) fun i _=>hg' i
  apply (mul_le_mul_of_nonneg_left h2 (one_dilate_pos w _ _).le).trans
  unfold pr oneBaseSheen; rw [←avg_mul']; refine avg_mono hν.nz fun i => ?_
  dsimp only
  by_cases h:H i
  · rw [show (H i ∧ Q i)=Q i from propext (and_iff_right h),ind_one h,mul_one]
    by_cases hp : Q i
    · rw [ind_one hp,mul_one]; exact hh i hp
    rw [ind_zero hp,mul_zero]
    exact (one_base_mirror_floor w t z o m s Y hu i).1
  rw [ind_zero h,ind_zero (show ¬ (H i∧ Q i) from fun hv=>h hv.1),mul_zero,mul_zero]

end OneQuill
end
end Lax793645Proofs.Simplifications
