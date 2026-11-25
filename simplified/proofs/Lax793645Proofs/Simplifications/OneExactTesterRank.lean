import Lax793645Proofs.Simplifications.OneCoherentQueryArrays
import Lax793645Proofs.Simplifications.OneFittedCoordinateBound
import Lax793645Proofs.Simplifications.CycleSupportConsistency
import Lax793645Proofs.Simplifications.LinearScreenSlopes

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {n N : ℕ}

theorem one_yoke_matrix (m : Mixer p n) (x : OneUnit p n N) (i : Bool)
    (u : Profile p n) (α : F) (K : ℕ) (hk : totalRank u≤K) (l : Tag p.g) :
    ∃ M : Moment p n,M.rank≤oneScreenRank p K ∧
      ∀ s f y,oneYoke m x i u α (useAtom p l s f y)=
        evmat M (spring p l s f y) (spring p l s f y)+
          (T0 p n u (useAtom p l s f y)+α*role p n (useAtom p l s f y)) := by
  obtain ⟨M,hM,ht⟩:=one_inner_gem x i l
  refine ⟨M+qmix m u l,?_,?_⟩
  · refine (mrk_add_le ..).trans ((Nat.add_le_add hM (qmix_rank ..)).trans ?_)
    unfold oneScreenRank
    change _+p.J*tagDegree p.g*(2*totalRank u)≤_
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left (p.J*tagDegree p.g)
      (Nat.mul_le_mul_left 2 hk)) _).trans_eq (by ring)
  intro s f y
  change oneInner x i (useAtom p l s f y)+
    (T0 p n u (useAtom p l s f y)+Tmix m u (useAtom p l s f y)+
      α*role p n (useAtom p l s f y))=_
  rw [show oneInner x i (useAtom p l s f y)=mpair M (mom p s (lit f l y)) from ht s _,
    show Tmix m u (useAtom p l s f y)=mpair (qmix m u l) (mom p s (lit f l y)) from Tmix_atom ..,
    ←mpair_outer,mpair_add]
  change mpair M (mom p s (lit f l y))+
    (T0 p n u (useAtom p l s f y)+mpair (qmix m u l) (mom p s (lit f l y))+
      α*role p n (useAtom p l s f y))=
    (mpair M (mom p s (lit f l y))+mpair (qmix m u l) (mom p s (lit f l y)))+
      (T0 p n u (useAtom p l s f y)+α*role p n (useAtom p l s f y))
  abel

theorem clean_role (E : Finset (Tag p.g)) (l : Tag p.g) (s : Label p.b)
    (y : Knobs p.g n) (hy : cleanInput p E y) :
    role p n (useAtom p l s Flavor.full y)=dialed p l Flavor.full y := by
  have hz:=clean_scan E y hy l (.inr ()) (by simp [retainedProbe])
  rw [role_scan]
  change (scan p l Flavor.full y).diagO=(scan p l Flavor.full y).diagO+
    scan p l Flavor.full y (.inr ())
  rw [hz,add_zero]

/-- Fix the common cell and test only the retained tester coordinates.
An exact identity bounds their number by the rank of its matrix. -/
theorem one_exact_cell_tester_rank (H : Space (OneJointKey p N))
    (o : OneOrient p n N) (s : Label p.b) (l : Tag p.g)
    (hfree : Injective ((oneMixedRow (oneFreeColumns p n s) o).comp H.subtype))
    (φ : Module.Dual F H→F) (E : Finset (Tag p.g)) (M : Moment p n)
    (m : Mixer p n) (hj : 1≤p.j) (hn : 2*p.r≤n)
    (he : ∀ y,cleanInput p E y→
      φ (oneQueryCell H o l s Flavor.full y)=dialed p l Flavor.full y+
        evmat M (spring p l s Flavor.full y) (spring p l s Flavor.full y)) :
    privateWidth p.g*(p.g-E.card)*p.r≤2*M.rank := by
  classical
  by_contra hroom
  have hroom : 2*M.rank+1≤privateWidth p.g*(p.g-E.card)*p.r:=by omega
  let d:=2*M.rank+1
  let f:=Flavor.full (g:=p.g)
  let A0:=(oneJointCell H).comp (oneFreeKey (oneFreeColumns p n s) o)
  obtain ⟨S,hS⟩:=A0.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (one_joint_cell_free_surjective _ o H hfree))
  have hS' (c : Module.Dual F H) : A0 (S c)=c:=LinearMap.congr_fun hS c
  obtain ⟨a,ha,hclean⟩:=masked_punch_real p l E (beamMap d)
    ((beam_rank_le d).trans (hroom.trans (coordinate_tester_room p l E)))
  have hμ:=sketch_law p n a hn
  obtain ⟨x,_,hx⟩:=exists_of_pr_pos (p:=fun _=>True) hμ.nz
    (by rw [pr_true,hμ.total]; norm_num)
  let y:=fun i=>oneRecenterQuery H o l s f S (x i) 0
  have hy : sketchLaw p n a y≠0 := by
    rw [show sketchLaw p n a y=sketchLaw p n a x from
      one_recenter_sketch_weight H o l s f S a x 0]
    exact hx.ne'
  let A:=incision p l s f y
  let Q:=pullM A A M
  let ψ (u : Vec (Hue d)):=φ 0+evmat (beamMap d) u u
  have hgram : pullM A A (selfM p n m.mixM)=beamMap d:=
    (sketch_matrix p l s f m a hj y hy).trans ha
  have hcell (u : Vec (Hue d)) (hu : weightsAff u) :
      oneQueryCell H o l s f (compound p y u)=0 := by
    rw [show compound p y u=oneRecenterQuery H o l s f S (compound p x u) 0 from
      one_recenter_query_compound H o l s f S x u hu 0]
    exact one_recenter_query_cell H o l s f S hS' _ _
  have hval (u : Vec (Hue d)) (hu : weightsAff u) : ψ u=evmat Q u u := by
    let z:=compound p y u
    have hq : evmat (beamMap d) u u=dialed p l f z := by
      rw [←hgram]
      exact inc_diag p l s f m y u hu hj
    have hh:=he z (clean_compound E a hclean y hy u)
    rw [hcell u hu] at hh
    change φ 0+evmat (beamMap d) u u=evmat Q u u
    rw [hq,hh,add_right_comm,char_two,zero_add,evmat_pull,
      inc_compound p l s f y u hu]
  have harches : arches ψ=1:=(arches_constant_add _ _).trans (arches_beam d)
  have hrank:=(arches_rank ψ Q hval).trans
    (Nat.mul_le_mul_left 2 (rank_lift_le Aᵀ Aᵀ M))
  rw [harches,Matrix.rank_one,Fintype.card_fin] at hrank
  dsimp only [d] at hrank
  omega

/-- Each nonzero coefficient consumes a full private tester block.
This support estimate is intrinsic to the marked profile. -/
theorem one_exact_tester_support (H : Space (OneJointKey p N))
    (x : OneUnit p n N) (i : Bool) (u : Profile p n) (α γ : F)
    (m : Mixer p n) (K : ℕ) (hk : totalRank u≤K) (hg : Odd p.g) (h3 : 2≤p.g)
    (s : Label p.b) (l : Tag p.g)
    (hfree : Injective ((oneMixedRow (oneFreeColumns p n s) (x i)).comp H.subtype))
    (φ : Module.Dual F H→F) (hj : 1≤p.j) (hn : 2*p.r≤n)
    (he : ∀ y,oneYoke m x i u α (useAtom p l s Flavor.full y)=
      φ (oneQueryCell H (x i) l s Flavor.full y)+γ*dialed p l Flavor.full y) :
    (bitSupport (fun t=>testerCoefficients u α t+γ)).card*p.r≤2*oneScreenRank p K := by
  classical
  let d:=fun t=>testerCoefficients u α t+γ
  let E:=(univ : Finset (Tag p.g)).filter (fun t=>d t=0)
  obtain ⟨M,hM,hmat⟩:=one_yoke_matrix m x i u α K hk l
  have hcore (y : Knobs p.g n) (hy : cleanInput p E y) :
      T0 p n u (useAtom p l s Flavor.full y)+
        (α+γ)*role p n (useAtom p l s Flavor.full y)=dialed p l Flavor.full y := by
    apply coreRole p u E (α+γ) hg _ l s y hy
    intro t ht
    have hd : d t≠0 := by simpa only [E,mem_filter,mem_univ,true_and] using ht
    have hv : d t=1:=(bit_cases (d t)).resolve_left hd
    simpa only [d,testerCoefficients,add_assoc] using hv
  have hidentity (y : Knobs p.g n) (hy : cleanInput p E y) :
      φ (oneQueryCell H (x i) l s Flavor.full y)=dialed p l Flavor.full y+
        evmat M (spring p l s Flavor.full y) (spring p l s Flavor.full y) := by
    have hh:=(he y).symm.trans (hmat s Flavor.full y)
    have hc:=hcore y hy
    rw [clean_role E l s y hy] at hh hc
    linear_combination hh+hc-char_two (γ*dialed p l Flavor.full y)
  have hbound:=one_exact_cell_tester_rank H (x i) s l hfree φ E M m hj hn hidentity
  have hcard : p.g-E.card=(bitSupport d).card := by
    have hh:=Finset.card_filter_add_card_filter_not (s:=univ) (p:=fun t : Tag p.g=>d t=0)
    simp only [card_univ,Fintype.card_fin] at hh
    change E.card+(bitSupport d).card=p.g at hh
    omega
  rw [hcard,privateWidth_of_two_le h3,one_mul] at hbound
  exact hbound.trans (Nat.mul_le_mul_left 2 hM)

end
end Lax793645Proofs.Simplifications
