import Lax793645Proofs.Simplifications.OneBinaryQueryTests
import Lax793645Proofs.Simplifications.OnePaletteQueryCells
import Lax793645Proofs.Simplifications.OneConditionalStatusGap
import Lax793645Proofs.Simplifications.TwoPositionOverlap

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open LinearMap Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

private theorem croon_parts (v : Template p I) (i : I) (a : Knobs p.g n) :
    v.croon i a=springLinear p (v.t i) (v.s i) (v.f i) a+v.croon i 0 := by
  change _=(_-v.croon i 0)+v.croon i 0
  abel

private def slotKey (v : Template p I) (u : OneUnit p n N) (i : I) :=
  ((oneStarKey (v.t i)).comp (onePrimalKey (u (v.aim i)))).comp
    (springLinear p (v.t i) (v.s i) (v.f i) (n:=n))

private theorem slot_key_apply (v : Template p I) (u : OneUnit p n N) (i : I) (a : Knobs p.g n) :
    oneCallOne v i a (u (v.aim i))=slotKey v u i a+oneCallOne v i 0 (u (v.aim i)) := by
  change oneStarKey _ (onePrimalKey _ (v.croon i a))=_
  rw [croon_parts v i a,map_add,map_add]
  rfl

/-- The two star keys and every prescribed binary bit of one duet of the
query template. The two slots are sampled independently before unary checks. -/
def oneTwoPositionQuery (v : Template p I) (m : Mixer p n) (u : OneUnit p n N)
    (s : Script p I) (i : v.Chorus) :
    TwoPositionQuery (Knobs p.g n) (Knobs p.g n) (OneAtomKey (v.t (v.choral.first i)) N)
      (OneAtomKey (v.t (v.choral.nextP i)) N) (Fintype.card (oneAbbey v i)) := by
  let i₁:=v.choral.first i
  let i₂:=v.choral.nextP i
  let e : Fin (Fintype.card (oneAbbey v i)) ≃ oneAbbey v i := (Fintype.equivFin _).symm
  let B j:=(oneMonks v m u i (e j)).toBilin'
  refine ⟨slotKey v u i₁,slotKey v u i₂,
    (oneCallOne v i₁ 0 (u (v.aim i₁)),oneCallOne v i₂ 0 (u (v.aim i₂))),
    fun a b j=>oneChime v m u i a b (e j),?_,?_,fun j=>oneLyrics v s i (e j)⟩
  · intro b
    let L:=springLinear p (v.t i₁) (v.s i₁) (v.f i₁) (n:=n)
    refine ⟨LinearMap.pi (fun j=>((B j).flip (v.croon i₂ b)).comp L),
      fun j=>B j (v.croon i₁ 0) (v.croon i₂ b),?_⟩
    intro a
    funext j
    simp only [oneChime,evmat,←Matrix.toBilin'_apply']
    change B j (v.croon i₁ a) (v.croon i₂ b)=B j (L a) (v.croon i₂ b)+_
    rw [croon_parts v i₁ a,map_add,LinearMap.add_apply]
  · intro a
    let L:=springLinear p (v.t i₂) (v.s i₂) (v.f i₂) (n:=n)
    refine ⟨LinearMap.pi (fun j=>((B j) (v.croon i₁ a)).comp L),
      fun j=>B j (v.croon i₁ a) (v.croon i₂ 0),?_⟩
    intro b
    funext j
    simp only [oneChime,evmat,←Matrix.toBilin'_apply']
    change B j (v.croon i₁ a) (v.croon i₂ b)=B j (v.croon i₁ a) (L b)+_
    rw [croon_parts v i₂ b,map_add]

/-- The direct fiber lower bound counts the construction's prescribed
script on its actual keys, including both affine offsets. -/
theorem one_two_position_script_mass (v : Template p I) (m : Mixer p n)
    (u : OneUnit p n N) (s : Script p I) (i : v.Chorus) (k) :
    (oneTwoPositionQuery v m u s i).feasibleMass k ≤
      pr (pairW unif unif) (fun ab=>
        oneCallOne v (v.choral.first i) ab.1 (u (v.aim (v.choral.first i)))=k.1 ∧
        oneCallOne v (v.choral.nextP i) ab.2 (u (v.aim (v.choral.nextP i)))=k.2 ∧
        oneChime v m u i ab.1 ab.2=oneLyrics v s i) := by
  refine ((oneTwoPositionQuery v m u s i).feasible_le_accepted k).2.trans_eq ?_
  apply congrArg (pr (pairW unif unif))
  funext ab
  apply propext
  change (_=k.1-_ ∧ _=k.2-_ ∧ (fun j=>oneChime v m u i ab.1 ab.2 _)=_) ↔ _
  simp only [oneTwoPositionQuery,eq_sub_iff_add_eq,←slot_key_apply]
  apply and_congr_right'
  apply and_congr_right'
  constructor
  · intro h
    funext j
    simpa only [Equiv.symm_apply_apply] using congrFun h (Fintype.equivFin _ j)
  · intro h
    simp only [h]

open StatusAnalysis in
/-- At a feasible pair, imposing the full unary statuses on the two
original key fibers also costs only a construction constant. Inputs
are uniform knobs, before the protected base rejection. -/
theorem one_two_position_full_status_mass (v : Template p I) (m : Mixer p n)
    (u : OneUnit p n N) (s : Script p I) (i : v.Chorus) (hg : Odd p.g) (K : ℕ)
    {d₁ d₂ : ℕ} (V : Ax p n d₁) (W : Ax p n d₂) (hd : d₁≤K^2) (he : d₂≤K^2)
    (hV : ∀ j : Fin d₁,totalRank (V (Pi.single j 1))≤K)
    (hW : ∀ j : Fin d₂,totalRank (W (Pi.single j 1))≤K)
    (a b : Knobs p.g n) (hscript : oneChime v m u i a b=oneLyrics v s i) :
    let i₁:=v.choral.first i
    let i₂:=v.choral.nextP i
    let f j z:=oneCallOne v j z (u (v.aim j))
    let P:=oneSpecify p (v.aim i₁) V m u (v.t i₁) (v.s i₁) (v.f i₁)
    let Q:=oneSpecify p (v.aim i₂) W m u (v.t i₂) (v.s i₂) (v.f i₂)
    let c:=bp (-(oneStatusCoordinateBound p (K^2) K:ℝ))
    (bp (-(Fintype.card (oneAbbey v i):ℝ)))^2 *
        ((c*pr unif (fun x=>f i₁ x=f i₁ a))*(c*pr unif (fun y=>f i₂ y=f i₂ b))) ≤
      pr (pairW unif unif) (fun xy=>f i₁ xy.1=f i₁ a ∧ f i₂ xy.2=f i₂ b ∧
        P xy.1=P a ∧ Q xy.2=Q b ∧ oneChime v m u i xy.1 xy.2=oneLyrics v s i) := by
  intro i₁ i₂ f P Q c
  obtain ⟨r,hr,L,G,hL⟩:=one_status_coordinates_bounded hg (v.aim i₁) V m u (v.t i₁) (v.s i₁) (v.f i₁) K hd hV
  obtain ⟨t,ht,M,H,hM⟩:=one_status_coordinates_bounded hg (v.aim i₂) W m u (v.t i₂) (v.s i₂) (v.f i₂) K he hW
  let D:=oneTwoPositionQuery v m u s i
  have Hs : D.test a b=D.target := funext fun j=>congrFun hscript ((Fintype.equivFin _).symm j)
  have hp x (hx : L x=L a) : P x=P a := (hL () x).trans ((congrArg (G ()) hx).trans (hL () a).symm)
  have hq y (hy : M y=M b) : Q y=Q b := (hM () y).trans ((congrArg (H ()) hy).trans (hM () b).symm)
  have lower:=D.status_witness_mass L M _ _ a b hp hq Hs
  have keys (j : I) (x y : Knobs p.g n) : f j x=f j y ↔ slotKey v u j x=slotKey v u j y := by
    rw [show f j x=_ from slot_key_apply v u j x,show f j y=_ from slot_key_apply v u j y,add_left_inj]
  simp_rw [keys]
  have hr' : c≤bp (-(r:ℝ)) := bp_le (neg_le_neg (by exact_mod_cast hr))
  have ht' : c≤bp (-(t:ℝ)) := bp_le (neg_le_neg (by exact_mod_cast ht))
  refine le_trans ?_ (lower.trans ?_)
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply mul_le_mul (mul_le_mul_of_nonneg_right hr' (pr_nonneg unif_law.nz))
      (mul_le_mul_of_nonneg_right ht' (pr_nonneg unif_law.nz))
      (mul_nonneg (bp_pos _).le (pr_nonneg unif_law.nz))
      (mul_nonneg (bp_pos _).le (pr_nonneg unif_law.nz))
  apply pr_mono (pairW_law unif_law unif_law).nz
  rintro xy ⟨h₁,h₂,h₃,h₄,h₅⟩
  refine ⟨h₁,h₂,h₃,h₄,funext fun j=>?_⟩
  simpa only [D,oneTwoPositionQuery,Equiv.symm_apply_apply] using congrFun h₅ (Fintype.equivFin _ j)

open StatusAnalysis in
/-- An actual duet with requested unary statuses is a request to which
the filtered overlap theorem applies. The row bound precedes all leaf
choices. The identity holds for every key, including empty fibers. -/
theorem one_duet_status_request (v : Template p I) (m : Mixer p n) (u : OneUnit p n N)
    (s : Script p I) (i : v.Chorus) (hg : Odd p.g) (K : ℕ)
    {d e : ℕ} (V : Ax p n d) (W : Ax p n e) (hd : d≤K^2) (he : e≤K^2)
    (hV : ∀ j : Fin d,totalRank (V (Pi.single j 1))≤K)
    (hW : ∀ j : Fin e,totalRank (W (Pi.single j 1))≤K) (z : Magazine p d) (w : Magazine p e) :
    let i₁:=v.choral.first i
    let i₂:=v.choral.nextP i
    ∃ D : TwoPositionRequest (Knobs p.g n) (Knobs p.g n) (OneAtomKey (v.t i₁) N)
        (OneAtomKey (v.t i₂) N) (Fintype.card (oneAbbey v i)),
      D.toTwoPositionQuery=oneTwoPositionQuery v m u s i ∧
      D.leftCount≤oneStatusCoordinateBound p (K^2) K ∧ D.rightCount≤oneStatusCoordinateBound p (K^2) K ∧
      ∀ k,D.actual k=pr (pairW unif unif) (fun ab=>
        oneCallOne v i₁ ab.1 (u (v.aim i₁))=k.1 ∧ oneCallOne v i₂ ab.2 (u (v.aim i₂))=k.2 ∧
        oneSpecify p (v.aim i₁) V m u (v.t i₁) (v.s i₁) (v.f i₁) ab.1=z ∧
        oneSpecify p (v.aim i₂) W m u (v.t i₂) (v.s i₂) (v.f i₂) ab.2=w ∧
        oneChime v m u i ab.1 ab.2=oneLyrics v s i) := by
  intro i₁ i₂
  obtain ⟨r,hr,L,G,hL⟩:=one_status_coordinates_bounded hg (v.aim i₁) V m u (v.t i₁) (v.s i₁) (v.f i₁) K hd hV
  obtain ⟨t,ht,M,H,hM⟩:=one_status_coordinates_bounded hg (v.aim i₂) W m u (v.t i₂) (v.s i₂) (v.f i₂) K he hW
  let D:=oneTwoPositionQuery v m u s i
  refine ⟨⟨D,r,t,L,M,fun x=>G () x=z,fun y=>H () y=w⟩,rfl,hr,ht,?_⟩
  intro k
  apply congrArg (pr (pairW unif unif))
  funext ab
  apply propext
  change (slotKey v u i₁ ab.1=k.1-oneCallOne v i₁ 0 (u (v.aim i₁)) ∧
    slotKey v u i₂ ab.2=k.2-oneCallOne v i₂ 0 (u (v.aim i₂)) ∧
    G () (L ab.1)=z ∧ H () (M ab.2)=w ∧ D.test ab.1 ab.2=D.target) ↔ _
  rw [eq_sub_iff_add_eq,eq_sub_iff_add_eq,←slot_key_apply,←slot_key_apply,←hL () ab.1,←hM () ab.2]
  apply and_congr_right'
  apply and_congr_right'
  apply and_congr_right'
  apply and_congr_right'
  constructor
  · intro h
    funext j
    simpa only [D,oneTwoPositionQuery,Equiv.symm_apply_apply] using congrFun h (Fintype.equivFin _ j)
  intro h
  exact funext fun j=>congrFun h ((Fintype.equivFin _).symm j)

end
end Lax793645Proofs.Simplifications
