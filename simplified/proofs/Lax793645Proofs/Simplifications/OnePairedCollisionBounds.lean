import Lax793645Proofs.Simplifications.OneAcceptedCollisions
import Lax793645Proofs.Simplifications.OneOptionRealization
import Lax793645Proofs.Simplifications.OneOptionProtection
import Lax793645Proofs.Simplifications.OneStation

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem overlap_map_equiv {A B : Type} [Fintype A] [Fintype B]
    (E : A≃B) (ν u v : Wgt A) :
    overlap (mapW ν E) (mapW u E) (mapW v E)=overlap ν u v := by
  unfold overlap density avg
  simp_rw [mapW_equiv_val]
  exact E.symm.sum_comp (fun x:A=>ν x*(u x/ν x*(v x/ν x)))

private theorem uniform_weights_instances {A:Type} (i j:Fintype A) (P:A→Prop) :
    @unifOn A i P=@unifOn A j P := by
  cases Subsingleton.elim i j
  rfl

variable {p : Shape} {n N K : ℕ} {q : Format} {d e : Rates}

def oneClash (m : Mixer p n) (xy : OneUnit p n N×OneUnit p n N) :=
  (oneRawHoles m).conflict (xy.1 true,xy.1 false) (xy.2 true,xy.2 false)
def oneBeamPrice (p : Shape) (N : ℕ):=bp (((oneMaxSlots p:ℝ)+0.02)*(2*N))

structure OneEarnsScore (p : Shape) (n N K : ℕ) (ζ : ℝ) : Prop where
  hr : 1≤p.r
  hn : 2*p.r≤n
  odd : Odd p.g
  room : ∀ t≤28,oneRealizationRoom p K t
  smooth : 0≤ζ
  low : ζ≤0.004
  light : ζ*oneMaxSlots p≤0.004
  hN : 100≤2*N
  gram : (dim (OneCheckGram p n):ℝ)≤0.01*(2*N)
  budget : (K+(oneMaxSlots p:ℝ))*num (OneColumn p n)≤0.005*(2*N)

namespace OneStation
variable {pop : OneLeafMixture p n N} (v : OneStation p n N K pop)

set_option maxHeartbeats 1000000 in
theorem sellPoint (w : Typus p q d e) (m : Mixer p n) (μ : Wgt (OneUnit p n N))
    (i j:pop.T) (k:Fin (2^oneDeckMax p K)) {C ζ:ℝ}
    (hp : oneLeafStrength pop μ m C ζ K) (hw : IsLaw μ) (he : OneEarnsScore p n N K ζ) :
    v.matchScore w m μ i j k≤oneBeamPrice p N*
      pr (pairW (partW μ i.val) (partW μ j.val)) (oneClash m)+2*bp (-0.005*(2*N)) := by
  have hA:=hp.leaf i.val i.property
  have hB:=hp.leaf j.val j.property
  let a:=w.qA.pen w.t
  let b:=w.qB.pen w.t
  let ia:=pop.pin i.val
  let ib:=pop.pin j.val
  let u:=partW μ i.val
  let u':=partW μ j.val
  let F:=v.frontPage w m i j k
  let G:=v.backPage w m i j k
  let T:=v.mails i j k
  let s:=v.cAxes i d
  let t:=v.cAxes j e
  let U (z:Inputs p n (Messenger q)) (o:OneUnit p n N):=
    OneProtectedInput a ia.sp K z ∧ F o ∧ OneQuill.oneDeposit w.qA w.t w.z m o s z
  let V (z:Inputs p n (Messenger q)) (o:OneUnit p n N):=
    OneProtectedInput b ib.sp K z ∧ G o ∧ OneQuill.oneDeposit w.qB w.t w.z m o t z
  have hu : IsLaw u:=on_law hw.nz hA.pos
  have hu' : IsLaw u':=on_law hw.nz hB.pos
  let δ:=pr (pairW u u') (oneClash m)
  have hδ:0≤δ:=pr_nonneg (pairW_law hu hu').nz
  change overlap (unifOn (oneOwnPart w.t w.z))
    (mapW (oneHistogram a.draw w.t u (a.state w.z n) U) (oneQueryCoordinateEquiv w.t N).symm)
    (mapW (oneHistogram b.draw w.t u' (b.state w.z n) V) (oneQueryCoordinateEquiv w.t N).symm)≤_
  have href : mapW (oneLawNu p N w.t w.z) (oneQueryCoordinateEquiv w.t N).symm=
      unifOn (oneOwnPart (N:=N) w.t w.z):=
    (one_reference_coordinates w.t w.z).trans (uniform_weights_instances _ _ _)
  rw [←href,overlap_map_equiv]
  by_cases hg:v.news w i j k
  · have hfmt:=hg.1.1
    have hcount:=one_messenger_card (p:=p) (n:=n) hfmt
    have hslots : oneSlots p (Messenger q)≤oneMaxSlots p:=Nat.mul_le_mul_right _ hcount
    have hres:=one_collision_on_accepted_slots a.draw b.draw m
      (a.state w.z n) (b.state w.z n) U V
      (fun z x (h:U z x)=>⟨h.2.1.2.1,h.2.1.2.2.1⟩)
      (fun z x (h:V z x)=>⟨h.2.1.2.1,h.2.1.2.2.1⟩)
      (K:=K) (ζ:=ζ) ?_ ?_ ?_ hA.bound hB.bound he.low
      ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hslots) he.smooth).trans he.light)
      hslots hu.sub hu'.sub
      (quillState hg.1.2.1 he.hr he.hn).sub (quillState hg.1.2.2.1 he.hr he.hn).sub
      hA.clear hB.clear he.hN he.gram he.budget (oneOwnKeyPart w.t w.z)
    · apply hres.trans
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_right _ hδ
      apply bp_le
      apply mul_le_mul_of_nonneg_right _ (by positivity : 0≤(2:ℝ)*N)
      exact add_le_add (Nat.cast_le.mpr hslots) le_rfl
    · intro z z' x hx y hy hkey
      exact OneOptions.realize w m ia ib T s t he.odd hA.closed hB.closed hg
        (he.room _ hcount) z z' x y
        ⟨True.intro,hx.2.1.2⟩ ⟨True.intro,hy.2.1.2⟩ hx.1 hy.1 hx.2.2 hy.2.2 hkey
    · intro z x hx
      obtain ⟨hprot⟩:=hx.1
      exact one_protected_key_rank (a.draw z) w.t ia.sp _ hprot
    · intro z x hx
      obtain ⟨hprot⟩:=hx.1
      exact one_protected_key_rank (b.draw z) w.t ib.sp _ hprot
  · have hz (key):oneHistogram a.draw w.t u (a.state w.z n) U key=0:=by
      unfold oneHistogram inputHistogram
      have ht z : pr u (fun x=>U z x ∧ oneVolleyKeys (a.draw z) w.t x=key)=0:=by
        have hf : (fun x=>U z x ∧ oneVolleyKeys (a.draw z) w.t x=key)=(fun _=>False):=
          funext fun x=>propext ⟨fun h=>hg h.1.2.1.1,False.elim⟩
        rw [hf,pr_false]
      simp_rw [ht]
      simp
    unfold overlap density
    simp only [hz,zero_div,zero_mul,avg_const,mul_zero]
    exact add_nonneg (mul_nonneg (bp_pos _).le hδ) (mul_nonneg (by norm_num) (bp_pos _).le)

theorem arena_bound (w : Typus p q d e) (m : Mixer p n) (μ : Wgt (OneUnit p n N))
    (k:Fin (2^oneDeckMax p K)) {C ζ:ℝ}
    (hp : oneLeafStrength pop μ m C ζ K) (hw : IsLaw μ)
    (h : 0<pop.amount μ) (he : OneEarnsScore p n N K ζ) :
    v.arena w m μ k≤oneBeamPrice p N*pr (pairW (pop.sap μ) (pop.sap μ)) (oneClash m)+
      2*bp (-0.005*(2*N)) := by
  obtain ⟨hx,hy⟩:=rebuild hw.nz hp.part (fun i hi=>(hp.leaf i hi).pos) h
  let t:=portionW μ pop.T
  have hm : IsLaw (pairW t t):=pairW_law hx hx
  refine (avg_mono hm.nz (fun x=>v.sellPoint w m μ x.1 x.2 k hp hw he)).trans_eq ?_
  rw [avg_add,avg_mul',hm.avg_const]
  change pop.sap μ=_ at hy
  rw [hy,←mix_data]
  unfold pr
  congr 1
  rw [mixW_avg]

end OneStation
end
end Lax793645Proofs.Simplifications
