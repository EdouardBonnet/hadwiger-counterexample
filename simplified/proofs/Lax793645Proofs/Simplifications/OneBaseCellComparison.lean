import Lax793645Proofs.Simplifications.OneBaseQueries
import Lax793645Proofs.Simplifications.OneSurrogateProductBounds
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SurrogateProductBounds

/-! Direct comparison for base predicates. Internal status bits are never enumerated. -/

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Filter Finset Matrix Function
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r : ℕ} {q : Format} {d : Rates} {b : Bool}
namespace OneQuill
variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : OneUnit p n N) (m : Mixer p n) (s : Charts p n d) (Y : OneSilhouette p N r)
  (U : Messenger q→Fin r→ℝ)

theorem one_base_prowl_linear_sum {I : Type} [Fintype I]
    (c : Wgt I) (W : I→Wgt (OneKeys t N)) :
    oneBaseProwl w t z s m o (fun x=>∑ i,c i*W i x)=
      ∑ i,c i*oneBaseProwl w t z s m o (W i) := by
  unfold oneBaseProwl
  simp only [Finset.mul_sum,avg_sum]
  apply sum_congr rfl
  intro i _
  rw [←avg_mul']
  exact avg_congr (fun x _=>by ring)

theorem one_base_sheen_linear_sum {I : Type} [Fintype I]
    (c : Wgt I) (W : I→Wgt (OneKeys t N)) :
    oneBaseSheen w t z o m s Y (fun x=>∑ i,c i*W i x)=
      ∑ i,c i*oneBaseSheen w t z o m s Y (W i) := by
  unfold oneBaseSheen
  simp only [Finset.mul_sum,avg_sum]
  apply sum_congr rfl
  intro i _
  rw [←avg_mul']
  exact avg_congr (fun x _=>by ring)

def oneBaseCellInput (i : Messenger q) (x : Knobs p.g n):=
  ind (w.sameInk i (OneAppearance.oneProfile (w.allure t z i) (parcel b i) o m (s (parcel b i)) x)) *
    U i (OneAppearance.oneShowTag (w.allure t z i) Y (o (parcel b i)) x)
def oneBaseCellShade (i : Messenger q) : Wgt (OneAtomKey (p:=p) (t i) N):=fun k=>
  oneCellTest t z Y U i k*oneBaseSeraph w t z o m s Y i k

theorem one_base_cell_input_bound (hU : ∀ i c,|U i c|≤1) (i : Messenger q) (x : Knobs p.g n) :
    |oneBaseCellInput w t z o m s Y U i x|≤1 := by
  rw [oneBaseCellInput,abs_mul]
  exact (mul_le_mul (by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _) (hU _ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem one_base_cell_shade_bound (hU : ∀ i c,|U i c|≤1) (i : Messenger q)
    (hκ : IsLaw (w.policies t z n i)) (x : OneAtomKey (p:=p) (t i) N) :
    |oneBaseCellShade w t z o m s Y U i x|≤1 := by
  have hh:=one_base_seraph_floor w t z o m s Y i hκ x
  rw [oneBaseCellShade,abs_mul,abs_of_nonneg hh.1]
  exact (mul_le_mul (hU _ _) hh.2 hh.1 zero_le_one).trans_eq (one_mul _)

theorem one_base_cell_surrogate_close (hU : ∀ i c,|U i c|≤1) (i : Messenger q)
    (hκ : IsLaw (w.policies t z n i)) {ε : ℝ}
    (hclose : OneAppearance.oneClose (w.allure t z i) Y (o (parcel b i)) ε) :
    |avg (oneLawOmega p N (t i) (z i)) (oneBaseCellShade w t z o m s Y U i)-
      avg (w.policies t z n i) (oneBaseCellInput w t z o m s Y U i)|≤ε := by
  let a:=w.allure t z i
  let j:=parcel b i
  let f (c : Fin r) (v : Magazine p (d j)):=U i c*ind (w.sameInk i v)
  have hf c v : |f c v|≤1 := by
    dsimp only [f]
    rw [abs_mul,abs_of_nonneg (ind_nonneg _)]
    exact (mul_le_mul (hU _ _) (ind_le_one _) (ind_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hh:=OneAppearance.oneClose_expect a Y j o m (s j) hκ f hf hclose
  have he : avg (OneAppearance.oneReference a Y)
      (fun c=>avg (OneAppearance.oneReflected a Y j o m (s j) c) (f c))=
      avg (oneLawOmega p N (t i) (z i)) (oneBaseCellShade w t z o m s Y U i) := by
    unfold OneAppearance.oneReference
    rw [mapW_avg]
    apply avg_congr
    intro k _
    change avg _ (fun v=>U i (Y (t i) (z i) k)*ind (w.sameInk i v))=_
    rw [avg_mul']
    rfl
  rw [he] at hh
  have hc (x : Knobs p.g n) :
      f (OneAppearance.oneShowTag a Y (o j) x) (OneAppearance.oneProfile a j o m (s j) x)=
        oneBaseCellInput w t z o m s Y U i x := mul_comm _ _
  simp_rw [hc] at hh
  exact hh

theorem one_base_cell_sheen :
    oneBaseSheen w t z o m s Y (prodW (oneCellTest t z Y U))=
      oneKappa (w.pen t)*avg (oneLawNu p N t z) (prodW (oneBaseCellShade w t z o m s Y U)) := by
  unfold oneBaseSheen oneBaseMirror
  rw [←avg_mul']
  apply avg_congr
  intro x _
  simp only [oneBaseCellShade,prodW,Finset.prod_mul_distrib]
  ring

theorem one_base_cell_prowl (hframe : ∀ i,oneFrameLaw m (o i)) (hm : ReducedMixerLaw m) (hj : 1≤p.j) :
    oneBaseProwl w t z s m o (prodW (oneCellTest t z Y U))=
      avg (prodW (w.policies t z n)) (fun x=>ind (onePerforms (w.pen t) w.script m o x)*
        prodW (oneBaseCellInput w t z o m s Y U) x) := by
  unfold oneBaseProwl oneBaseDeposit
  apply avg_congr
  intro x hx
  change (∏ i : Messenger q,w.policies t z n i (x i))≠0 at hx
  have hq (i : Messenger q) : dialed p (t i) (w.flav i) (x i)=z i := by
    have hi : w.policies t z n i (x i)≠0:=Finset.prod_ne_zero_iff.mp hx i (mem_univ i)
    exact (onW_ne hi).1
  have hp:=one_performs_own (w.pen t) w.script m o x hframe hm hj z hq
  have hpaint : prodW (fun i y=>ind (w.sameInk i
      (OneAppearance.oneProfile (w.allure t z i) (parcel b i) o m (s (parcel b i)) y))) x=
      ind (∀ i,w.sameInk i (onePrinted b s t w.sel w.flav m o x i)) := by
    rw [ind_all]
    rfl
  rw [hp,ind_and,←hpaint]
  have he : prodW (oneBaseCellInput w t z o m s Y U) x=
      prodW (fun i y=>ind (w.sameInk i (OneAppearance.oneProfile (w.allure t z i) (parcel b i) o m (s (parcel b i)) y))) x*
      prodW (oneCellTest t z Y U) (oneVolleyKeys ((w.pen t).draw x) t o) := by
    exact Finset.prod_mul_distrib
  rw [he]
  simp only [ind_and]
  dsimp only [Quill.pen,manager]
  ring

/-- Compare the base predicates directly, without enumerating internal status bits. -/
theorem one_base_cell_query_comparison (hU : ∀ i c,|U i c|≤1)
    (hκ : ∀ i,IsLaw (w.policies t z n i)) (hframe : ∀ i,oneFrameLaw m (o i))
    (hj : 1≤p.j) (hm : reducedBinaryGood m) (hfire : oneLitFire o) (hsel : (w.pen t).diffsel)
    (C : ℝ) (hC : 0<C) (hcap : ∀ i x,w.policies t z n i x≤C*unif x)
    {ε : ℝ} (hclose : ∀ i,OneAppearance.oneClose (w.allure t z i) Y (o (parcel b i)) ε)
    (hN : 2*num ((Messenger q)×Toast p)+2≤(N:ℝ)) :
    |oneBaseProwl w t z s m o (prodW (oneCellTest t z Y U))-
      oneBaseSheen w t z o m s Y (prodW (oneCellTest t z Y U))|≤
      C^2*bp (-(n:ℝ)/10)+num (Messenger q)*ε+
        2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2) := by
  let A i:=avg (w.policies t z n i) (oneBaseCellInput w t z o m s Y U i)
  let B i:=avg (oneLawOmega p N (t i) (z i)) (oneBaseCellShade w t z o m s Y U i)
  have hΩ i : IsLaw (oneLawOmega p N (t i) (z i)) := by
    let : Nonempty (Messenger q):=⟨i⟩
    apply one_omega_law
    have ht : num (Toast p)≤num ((Messenger q)×Toast p) := by
      simpa only [num,Fintype.card_prod,Nat.cast_mul] using
        (show (Fintype.card (Toast p):ℝ)≤Fintype.card (Messenger q)*Fintype.card (Toast p) by
          have hi : (1:ℝ)≤Fintype.card (Messenger q):=by exact_mod_cast Fintype.card_pos
          nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (Toast p))])
    linarith
  have ha i : |A i|≤1 := (abs_avg_le (hκ i).nz).trans
    ((hκ i).avg_le (one_base_cell_input_bound w t z o m s Y U hU i))
  have hb i : |B i|≤1 := (abs_avg_le (hΩ i).nz).trans
    ((hΩ i).avg_le (one_base_cell_shade_bound w t z o m s Y U hU i (hκ i)))
  have hab i : |A i-B i|≤ε := by
    rw [abs_sub_comm]
    exact one_base_cell_surrogate_close w t z o m s Y U hU i (hκ i) (hclose i)
  have hp:=cottonError univ A B ε ha hb hab
  have hκtop:=one_kappa_top w t
  have hκpos:=(one_kappa_pos (w.pen t)).le
  have hp' : |oneKappa (w.pen t)*∏ i,A i-oneKappa (w.pen t)*∏ i,B i|≤num (Messenger q)*ε := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hκpos]
    exact ((mul_le_mul_of_nonneg_right hκtop (abs_nonneg _)).trans_eq (one_mul _)).trans hp
  have hr:=one_resonant (w.pen t) m hm o hfire hsel (w.policies t z n) hκ C hC hcap w.script
    (oneBaseCellInput w t z o m s Y U) (one_base_cell_input_bound w t z o m s Y U hU)
  rw [←one_base_cell_prowl w t z o m s Y U hframe hm.1 hj] at hr
  have href:=one_reference_product t z (oneBaseCellShade w t z o m s Y U)
    (fun i=>one_base_cell_shade_bound w t z o m s Y U hU i (hκ i)) hN
  have href' : |oneKappa (w.pen t)*∏ i,B i-
      oneBaseSheen w t z o m s Y (prodW (oneCellTest t z Y U))|≤
      2*quadraticNetFact (trayPort p t)*bp (-(N:ℝ)/2) := by
    rw [one_base_cell_sheen,←mul_sub,abs_mul,abs_of_nonneg hκpos]
    exact ((mul_le_mul_of_nonneg_right hκtop (abs_nonneg _)).trans_eq (one_mul _)).trans
      (by rw [abs_sub_comm]; exact href)
  exact (abs_sub_le _ _ _).trans ((add_le_add hr
    ((abs_sub_le _ _ _).trans (add_le_add hp' href'))).trans_eq (by ring))

end OneQuill
end
end Lax793645Proofs.Simplifications
