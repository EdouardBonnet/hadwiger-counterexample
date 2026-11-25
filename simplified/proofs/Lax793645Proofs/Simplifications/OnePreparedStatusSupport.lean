import Lax793645Proofs.Simplifications.OneFullPaletteStatusGap
import Lax793645Proofs.Simplifications.OneFiniteDualSystems
import Lax793645Proofs.Simplifications.ExactStatusDuality

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis OneAppearance Function LinearMap Finset
open StatusAnalysis.DualAnalysis
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N c R : ℕ}

def OnePaletteGood (H : Space (OneJointKey p N)) (o : OneUnit p n N) : Prop :=
  ∀ i s,Injective ((oneMixedRow (oneFreeColumns p n s) (o i)).comp H.subtype)

def OneFullTableGap (Y : OneSilhouette p N c) (m : Mixer p n) (K : ℕ)
    (o o' : OneUnit p n N) : Prop :=
  ∀ d d',d≤K^2→d'≤K^2→∀ i i',∀ v : Ax p n d,∀ v' : Ax p n d',
    (∀ j : Fin d,totalRank (v (Pi.single j 1))≤K)→
    (∀ j : Fin d',totalRank (v' (Pi.single j 1))≤K)→
    ∀ l q a b f f',
      (⟨l,a,f,q⟩ : Appearance p).apt→(⟨l,b,f',q⟩ : Appearance p).apt→
      ∀ z : Magazine p d,∀ z' : Magazine p d',z.1.sumBit=q→z'.1.sumBit=q→
        let x : Appearance p:=⟨l,a,f,q⟩
        let y : Appearance p:=⟨l,b,f',q⟩
        let overlap:=avg (oneReference x Y) (fun j=>
          oneReflected x Y i o m v j z*oneReflected y Y i' o' m v' j z')
        overlap=0 ∨ bp (-(4*(oneStatusCoordinateBound p (K^2) K:ℝ)+1))≤overlap

/-- One bounded ambient row space certifies the gap simultaneously for
every allowed basis, status, label, and pair of good orientations. -/
theorem one_palette_support_space (hg : Odd p.g) (hp : 1≤p.r) (hn : 2*p.r≤n)
    (Y : OneSilhouette p N c) (hY : OneFullLinearSilhouette Y R)
    (m : Mixer p n) (K : ℕ)
    (hN : ∀ l : Tag p.g,bp (-(N:ℝ)/2)≤bp (-num (oneUnaryRail (p:=p) l))/2)
    (hsmall : ∀ l : Tag p.g,2*bp (num (oneUnaryRail (p:=p) l))*bp (-(N:ℝ)/2)≤bp (-(R:ℝ))/2) :
    ∃ H : Space (OneJointKey p N),dim H≤p.g*R ∧
      ∀ o o',OnePaletteGood H o→OnePaletteGood H o'→OneFullTableGap Y m K o o' := by
  classical
  obtain ⟨r,hr,L,hL,ι,hι,he,H,hH,B,hB,hfactor⟩:=one_full_palette_coordinates Y hY
  refine ⟨H,hH,?_⟩
  intro o o' ho ho' d d' hd hd' i i' v v' hv hv' l q a b f f' hx hy z z' hq hq'
  have hrow : bp (-(R:ℝ))/2≤bp (-(r l:ℝ))/2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply bp_le
    exact neg_le_neg (by exact_mod_cast hr l)
  apply one_full_palette_status_gap hg K hd hd' Y l q a b f f' hx hy hp hn
    i i' o o' m v v' hv hv' z z' hq hq' (L l) (hL l) (ι l q) (hι l q)
    (he l q) _ _ (hN l) ((hsmall l).trans hrow)
  · exact one_palette_free_surjective H l (L l) (B l) (hB l) (hfactor l)
      (oneFreeColumns p n a) (o i) (ho i a)
  · exact one_palette_free_surjective H l (L l) (B l) (hB l) (hfactor l)
      (oneFreeColumns p n b) (o' i') (ho' i' b)

/-- The exceptional mass is charged under the prepared mixed marginal,
before any leaf pair or acceptance filter is selected. -/
theorem one_palette_good_mass (m : Mixer p n)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (hN : 4≤N)
    (H : Space (OneJointKey p N)) (U : Wgt (OneUnit p n N)) (hU : IsLaw U)
    (hcap : ∀ i o,mapW U (fun x=>x i) o≤bp ((n:ℝ)/32)*oneRaw m N o) :
    pr U (fun o=>¬OnePaletteGood H o)≤
      16*bp ((dim H:ℝ)+p.b-31*(n:ℝ)/32) := by
  classical
  have he : (fun o : OneUnit p n N=>¬OnePaletteGood H o)=
      (fun o=>∃ i,∃ s,¬Injective ((oneMixedRow (oneFreeColumns p n s) (o i)).comp H.subtype)) := by
    funext o
    simp only [OnePaletteGood,not_forall]
  rw [he]
  have hb (i : Nodes) : pr U (fun o=>∃ s,
      ¬Injective ((oneMixedRow (oneFreeColumns p n s) (o i)).comp H.subtype))≤
      8*bp ((dim H:ℝ)+p.b-31*(n:ℝ)/32) := by
    have hh:=one_prepared_linear_rank m hroom hN H (mapW U (fun x=>x i)) (hcap i)
    rw [mapW_pr] at hh
    exact hh
  refine (pr_exists_le hU.nz _).trans ((sum_le_sum fun i _=>hb i).trans_eq ?_)
  simp only [sum_const,card_univ,Nodes,Fintype.card_bool,nsmul_eq_mul]
  ring

/-- Transfer the actual-table gap to the scalar system's support
interface. Incompatible diagonal statuses have exactly zero weight. -/
theorem one_table_gap_dual {d d' : Rates} (Y : OneSilhouette p N c)
    (m : Mixer p n) (K : ℕ) (o o' : OneUnit p n N)
    (h : OneFullTableGap Y m K o o') (v : Charts p n d) (v' : Charts p n d')
    (hd : ∀ i,d i≤K^2) (hd' : ∀ i,d' i≤K^2)
    (hv : ∀ i j,totalRank (v i (Pi.single j 1))≤K)
    (hv' : ∀ i j,totalRank (v' i (Pi.single j 1))≤K) :
    HasStatusSupportGap (oneWisp p Y) (oneWake p Y m o v) (oneWake p Y m o' v')
      (bp (-(4*(oneStatusCoordinateBound p (K^2) K:ℝ)+1))) := by
  intro x hx i z
  by_cases hz : z.1.1.sumBit=x.q
  · by_cases hz' : z.2.1.sumBit=x.q
    · exact h (d i.1) (d' i.2) (hd _) (hd' _) i.1 i.2 (v i.1) (v' i.2)
        (hv _) (hv' _) x.l x.q (x.s true) (x.s false) (x.f true) (x.f false)
        (hx true) (hx false) z.1 z.2 hz hz'
    left
    have hzero (j : Fin c) : oneReflected (x.aspect false) Y i.2 o' m (v' i.2) j z.2=0 :=
      oneRefInk (x.aspect false) Y i.2 o' m (v' i.2) j z.2 (fun hf=>hz' hf.2.1)
    change avg (oneWisp p Y x.l x.q) (fun j=>
      oneReflected (x.aspect true) Y i.1 o m (v i.1) j z.1*
        oneReflected (x.aspect false) Y i.2 o' m (v' i.2) j z.2)=0
    simp only [hzero,mul_zero,avg_zero]
  left
  have hzero (j : Fin c) : oneReflected (x.aspect true) Y i.1 o m (v i.1) j z.1=0 :=
    oneRefInk (x.aspect true) Y i.1 o m (v i.1) j z.1 (fun hf=>hz hf.2.1)
  change avg (oneWisp p Y x.l x.q) (fun j=>
    oneReflected (x.aspect true) Y i.1 o m (v i.1) j z.1*
      oneReflected (x.aspect false) Y i.2 o' m (v' i.2) j z.2)=0
  simp only [hzero,zero_mul,avg_zero]

end
end Lax793645Proofs.Simplifications
