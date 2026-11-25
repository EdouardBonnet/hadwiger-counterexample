import Lax793645Proofs.Simplifications.OneSupportQueryScores

/-! Unary concentration and binary mixing give one-sided domination for products of support indicators. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function LinearMap Finset StatusAnalysis Filter
open scoped Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace OneQuill
variable {p : Shape} {n N r : ℕ} {q : Format} {d : Rates} {b : Bool}
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : OneUnit p n N) (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)

variable (θ : ℝ) (U : Messenger q→Fin r→ℝ)
def oneSupportCellShade (i : Messenger q) : Wgt (OneAtomKey (p:=p) (t i) N):=
  fun x=>oneCellTest t z Y U i x*oneSupportSeraph w t z o m s Y θ i x

theorem one_support_cell_shade_bound (hθ : 0≤θ ∧ θ≤1)
    (hU : ∀ i c,0≤U i c ∧ U i c≤1) (i : Messenger q) (x : OneAtomKey (p:=p) (t i) N) :
    0≤oneSupportCellShade w t z o m s Y θ U i x ∧
      oneSupportCellShade w t z o m s Y θ U i x≤1 := by
  have hh:=support_lower_bounds θ (oneSeraph w t z o m s Y i x) hθ
  exact ⟨mul_nonneg (hU _ _).1 hh.1,
    (mul_le_mul (hU _ _).2 hh.2 hh.1 zero_le_one).trans_eq (one_mul _)⟩

theorem one_support_cell_domination
    (hU : ∀ i c,0≤U i c ∧ U i c≤1) (i : Messenger q)
    (hκ : IsLaw (w.policies t z n i)) {ε : ℝ}
    (hclose : OneAppearance.oneClose (w.allure t z i) Y (o (parcel b i)) ε)
    (hdom : ∀ k,oneSupportSeraph w t z o m s Y θ i k≤oneSeraph w t z o m s Y i k) :
    avg (oneLawOmega p N (t i) (z i)) (oneSupportCellShade w t z o m s Y θ U i)-
      avg (w.policies t z n i) (oneCellInput w t z o m s Y U i)≤ε := by
  let a:=w.allure t z i
  let j:=parcel b i
  let f (c : Fin r) (v : Magazine p (d j)):=U i c*ind (v=w.amp i)
  have hf c v : |f c v|≤1 := by
    dsimp only [f]
    rw [abs_mul,abs_of_nonneg (ind_nonneg _),abs_of_nonneg (hU _ _).1]
    exact (mul_le_mul (hU _ _).2 (ind_le_one _) (ind_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hh:=OneAppearance.oneClose_expect a Y j o m (s j) hκ f hf hclose
  have he : avg (OneAppearance.oneReference a Y)
      (fun c=>avg (OneAppearance.oneReflected a Y j o m (s j) c) (f c))=
      avg (oneLawOmega p N (t i) (z i)) (oneCellShade w t z o m s Y U i) := by
    unfold OneAppearance.oneReference
    rw [mapW_avg]
    apply avg_congr
    intro k _
    change avg _ (fun v=>U i (Y (t i) (z i) k)*ind (v=w.amp i))=_
    rw [avg_mul']
    change _*pr _ _=_
    rw [pr_point']
    rfl
  rw [he] at hh
  have hc (x : Knobs p.g n) :
      f (OneAppearance.oneShowTag a Y (o j) x) (OneAppearance.oneProfile a j o m (s j) x)=
        oneCellInput w t z o m s Y U i x := mul_comm _ _
  simp_rw [hc] at hh
  change |avg (oneLawOmega p N (t i) (z i)) (oneCellShade w t z o m s Y U i)-
    avg (w.policies t z n i) (oneCellInput w t z o m s Y U i)|≤ε at hh
  have hmono : avg (oneLawOmega p N (t i) (z i))
      (oneSupportCellShade w t z o m s Y θ U i)≤
      avg (oneLawOmega p N (t i) (z i)) (oneCellShade w t z o m s Y U i) :=
    avg_mono (map_nz (unifOn_sub _).nz _) (fun k=>mul_le_mul_of_nonneg_left (hdom k) (hU _ _).1)
  linarith only [hmono,le_abs_self
    (avg (oneLawOmega p N (t i) (z i)) (oneCellShade w t z o m s Y U i)-
      avg (w.policies t z n i) (oneCellInput w t z o m s Y U i)),hh]

theorem one_support_cell_sheen :
    oneSupportSheen w t z o m s Y θ (prodW (oneCellTest t z Y U))=
      oneKappa (w.pen t)*avg (oneLawNu p N t z)
        (prodW (oneSupportCellShade w t z o m s Y θ U)) := by
  unfold oneSupportSheen oneSupportMirror
  rw [←avg_mul']
  apply avg_congr
  intro x _
  simp only [oneSupportCellShade,prodW,prod_mul_distrib]
  ring

theorem one_support_cell_query_domination (hθ : 0≤θ ∧ θ≤1)
    (hU : ∀ i c,0≤U i c ∧ U i c≤1)
    (hκ : ∀ i,IsLaw (w.policies t z n i)) (hframe : ∀ i,oneFrameLaw m (o i))
    (hj : 1≤p.j) (hm : reducedBinaryGood m) (hfire : oneLitFire o) (hsel : (w.pen t).diffsel)
    (C : ℝ) (hC : 0<C) (hcap : ∀ i x,w.policies t z n i x≤C*unif x)
    {ε : ℝ} (hε : 0≤ε)
    (hclose : ∀ i,OneAppearance.oneClose (w.allure t z i) Y (o (parcel b i)) ε)
    (hdom : ∀ i k,oneSupportSeraph w t z o m s Y θ i k≤oneSeraph w t z o m s Y i k)
    (hN : 2*num ((Messenger q)×Toast p)+2≤(N:ℝ)) :
    oneSupportSheen w t z o m s Y θ (prodW (oneCellTest t z Y U))-
      oneProwl w t z o m s (prodW (oneCellTest t z Y U))≤
      C^2*bp (-(n:ℝ)/10)+num (Messenger q)*ε+
        2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2) := by
  let A i:=avg (w.policies t z n i) (oneCellInput w t z o m s Y U i)
  let B i:=avg (oneLawOmega p N (t i) (z i)) (oneSupportCellShade w t z o m s Y θ U i)
  have hU' i c : |U i c|≤1:=by rw [abs_of_nonneg (hU i c).1]; exact (hU i c).2
  have hΩ i : IsLaw (oneLawOmega p N (t i) (z i)) := by
    let : Nonempty (Messenger q):=⟨i⟩
    apply one_omega_law
    have ht : num (Toast p)≤num ((Messenger q)×Toast p) := by
      simpa only [num,Fintype.card_prod,Nat.cast_mul] using
        (show (Fintype.card (Toast p):ℝ)≤Fintype.card (Messenger q)*Fintype.card (Toast p) by
          have hi : (1:ℝ)≤Fintype.card (Messenger q):=by exact_mod_cast Fintype.card_pos
          nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (Toast p))])
    linarith
  have ha i : 0≤A i ∧ A i≤1 := by
    refine ⟨avg_nonneg (hκ i).nz (fun x=>mul_nonneg (ind_nonneg _) (hU _ _).1),?_⟩
    exact (le_abs_self _).trans ((abs_avg_le (hκ i).nz).trans
      ((hκ i).avg_le (one_cell_input_bound w t z o m s Y U hU' i)))
  have hb i : 0≤B i ∧ B i≤1 :=
    ⟨avg_nonneg (hΩ i).nz (fun x=>(one_support_cell_shade_bound w t z o m s Y θ U hθ hU i x).1),
      (hΩ i).avg_le (fun x=>(one_support_cell_shade_bound w t z o m s Y θ U hθ hU i x).2)⟩
  have hab i : B i-A i≤ε:=
    one_support_cell_domination w t z o m s Y θ U hU i (hκ i) (hclose i) (hdom i)
  have hp:=product_domination_error A B ha hb ε hε hab
  have hp' : oneKappa (w.pen t)*∏ i,B i-oneKappa (w.pen t)*∏ i,A i≤num (Messenger q)*ε := by
    rw [←mul_sub]
    exact (mul_le_mul_of_nonneg_left hp (one_kappa_pos _).le).trans
      (mul_le_of_le_one_left (mul_nonneg (by unfold num; positivity) hε) (one_kappa_top w t))
  have hr:=one_resonant (w.pen t) m hm o hfire hsel (w.policies t z n) hκ C hC hcap w.script
    (oneCellInput w t z o m s Y U) (one_cell_input_bound w t z o m s Y U hU')
  rw [←one_cell_prowl w t z o m s Y U hframe hm.1 hj] at hr
  have href:=one_reference_product t z (oneSupportCellShade w t z o m s Y θ U)
    (fun i x=>by
      have hh:=one_support_cell_shade_bound w t z o m s Y θ U hθ hU i x
      rw [abs_of_nonneg hh.1]; exact hh.2) hN
  have href' : |oneSupportSheen w t z o m s Y θ (prodW (oneCellTest t z Y U))-
      oneKappa (w.pen t)*∏ i,B i|≤2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2) := by
    rw [one_support_cell_sheen,←mul_sub,abs_mul,abs_of_pos (one_kappa_pos _)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (one_kappa_top w t)).trans href
  have hr' := (abs_le.mp hr).1
  have href'' := (abs_le.mp href').2
  dsimp only [A,B] at hp'
  linarith only [hp',hr',href'']


end OneQuill

end
end Lax793645Proofs.Simplifications
