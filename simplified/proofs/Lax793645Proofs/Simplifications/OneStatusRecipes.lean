import Lax793645Proofs.Simplifications.ReducedOptions
import Lax793645Proofs.Simplifications.OneTableContracts
import Lax793645Proofs.Simplifications.OneStatusCharts
import Lax793645Proofs.Simplifications.OnePrintedStatusComparison
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.NumericalGradientTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Finset Matrix Function LinearMap Module Submodule
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}

def oneRegisters {r : ℕ} (i : Bool) (v : Ax p n r) (m : Mixer p n)
    (x : OneUnit p n N) : Profile p n→ₗ[F]Whole r where
  toFun z:=((role p n z,roll v (Tsym m z)),oneInner x i z)
  map_add' a b:=by rw [map_add,map_add,map_add]; congr 1
  map_smul' a b:=by rw [map_smul,map_smul,map_smul]; congr 1

theorem one_funds_reg (t : Tagging p (Messenger q)) (b : Bool) (v : Charts p n d)
    (m : Mixer p n) (o : OneUnit p n N) (l f x) (a : Amounts p q d b)
    (h : onePrinted b v t l f m o x=a) (i : Grid) :
    let j:=sendId b i
    let w:=(manager b t l f).draw x
    funds a i=oneRegisters j (v j) m o (unionAt (w.atomAt t) i) := by
  rw [←h]
  intro j w
  unfold funds unionAt
  rw [map_sum]
  rfl

def oneTargetMark (v : Charts p n d) (T : OneCross p n) (i j : Bool) : Cell (d i):=
  roll (v i) (oneContract T i j+role p n)
def oneHailing (v : Charts p n d) (w : Charts p n e) (T : OneCross p n) : Cabinet d e:=
  fun i=>(1,1,oneTargetMark v T i.1 i.2,oneTargetMark w (fun e=>(T e)ᵀ) i.2 i.1)
def oneStill (b : Bool) (a : Amounts p q d b) (v : Charts p n d) (T : OneCross p n) :=
  (∀ i:Grid,(funds a i).1.2=oneTargetMark v T (sendId b i) (sendId (!b) i)) ∧
    ∀ j:Bool,couple _ (funds a (transit b (true,j)))=
      couple _ (funds a (transit b (false,j)))

theorem one_spoken (v : Charts p n d) (w : Charts p n e) (T : OneCross p n)
    (z : Messenger q→F) (a : Amounts p q d true) (b : Amounts p q e false) :
    speak _ _ (sendSum z a b)=(oneHailing v w T,0) ↔
      (∀ i,fullq z i=1) ∧ rhyme a b ∧ oneStill true a v T ∧
        oneStill false b w (fun e=>(T e)ᵀ) := by
  let f i:=funds a i
  let g i:=funds b i
  let h1 i:=couple (d (sendId true i)) (f i)
  let h2 i:=couple (e (sendId false i)) (g i)
  rw [speak_val]
  simp_rw [sendSum_by]
  have h (x y:F) : x+y=0↔x=y := by rw [←ZModModule.sub_eq_add,sub_eq_zero]
  constructor
  · intro ht
    have hh:=congrArg Prod.fst ht
    have hx:=congrArg Prod.fst (congrArg Prod.snd ht)
    have hy:=congrArg Prod.snd (congrArg Prod.snd ht)
    refine ⟨fun i=>congrArg Prod.fst (congrFun hh i),
      fun i=>congrArg (fun x=>x.2.1) (congrFun hh i),
      ⟨fun i=>congrArg (fun x=>x.2.2.1) (congrFun hh i),fun i=>?_⟩,
      fun i=>congrArg (fun x=>x.2.2.2) (congrFun hh i),fun i=>?_⟩
    · have ht:=congrFun hx i
      change ∑ j:Bool,h1 (j,i)=0 at ht
      rw [Fintype.sum_bool,h] at ht
      exact ht
    · have ht:=congrFun hy i
      change ∑ j:Bool,h2 (i,j)=0 at ht
      rw [Fintype.sum_bool,h] at ht
      exact ht
  · rintro ⟨ht,hv,⟨hF,hA⟩,hG,hB⟩
    apply Prod.ext
    · funext i
      exact Prod.ext (ht i) (Prod.ext (hv i) (Prod.ext (hF i) (hG i)))
    apply Prod.ext
    · funext i
      change ∑ j:Bool,h1 (j,i)=0
      rw [Fintype.sum_bool,h]
      exact hA i
    · funext i
      change ∑ j:Bool,h2 (i,j)=0
      rw [Fintype.sum_bool,h]
      exact hB i

/-- Numerical basis equations imply the full effective-profile recipe.
The table-to-actual comparison is supplied by the opposite leaf's flag. -/
theorem one_still_recipe (t : Tagging p (Messenger q)) (b : Bool)
    (S : ImagePlan (Comp p.g) (OneColumn p n)) (T : OneCross p n)
    (v : Charts p n d) (ha : oneCharted v S) (m : Mixer p n)
    (o y : OneUnit p n N) (l f x) (a : Amounts p q d b)
    (h : onePrinted b v t l f m o x=a)
    (w : Volley p n (Messenger q)) (hw : w.obj=parcel (!b))
    (z : Messenger q→F) (hz : owing p b a z) (hq : ∀ i,fullq z i=1)
    (hh : oneStill b a v T)
    (hT : ∀ i j z,z∈oneEffectivePins (oneEndpointPrimalPins S) i→
      oneContract T i j z=oneFunctional (y j) (oneMomentEmbed (o i) z)) :
    OneScalarRecipe ((manager b t l f).draw x) w.obj t m o y (oneEndpointPrimalPins S) := by
  let u:=(manager b t l f).draw x
  have hi:=one_funds_reg t b v m o l f x a h
  have ho:u.obj=parcel b:=rfl
  have he (i j) (r : Grid) (hr:r=transit b (i,j)) : sendId b r=i ∧ sendId (!b) r=j := by
    have hh:=(sendPair b r).trans (show transit b r=(i,j) by rw [hr,transit_inv])
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  have ht (i j) : u.sumAt t w.obj i j=unionAt (u.atomAt t) (transit b (i,j)) := by
    obtain ⟨h1,h2⟩:=he i j _ rfl
    rw [hw,←sumAtSend b u t _ ho,h1,h2]
  constructor
  · have hu (i) : u.diagonalAt i=z i:=
      (etaScan p (t i) (l i) (f i) (x i)).symm.trans (by
        rw [←h] at hz
        exact hz i)
    intro i j
    obtain ⟨h1,h2⟩:=he i j _ rfl
    change ∑ a∈u.shoots w.obj i j,u.diagonalAt a=1
    simp_rw [hu]
    have hm:=sum_shots b u (transit b (i,j)) ho z
    rw [h1,h2,←hw] at hm
    exact hm.trans (hq _)
  · intro i j z hz
    let Z:=transit b (i,j)
    obtain ⟨h1,h2⟩:sendId b Z=i ∧ sendId (!b) Z=j:=he i j _ rfl
    let t':=sendId b Z
    obtain ⟨r,hr⟩:z∈LinearMap.range (v t') := by
      rw [(ha _).1]
      rwa [show t'=i from h1]
    have hg:=hh.1 Z
    rw [hi] at hg
    let W:=unionAt (u.atomAt t) Z
    have hgrad : Tsym m W z=oneContract T i j z+role p n z := by
      change roll (v t') (Tsym m W)=roll (v t') (oneContract T t' (sendId (!b) Z)+_) at hg
      have ht:=congrArg (fun x=>dotProduct x r) hg
      simp_rw [←roll_project,hr] at ht
      change Tsym m W z=oneContract T _ _ z+_ at ht
      rwa [show t'=i from h1,h2] at ht
    rw [ht,grad_val,hgrad,add_left_comm,char_two,add_zero]
    exact hT i j z hz

/-- The script existence argument uses only the finite parity equations. -/
theorem one_proclaim_script (b : Bool) (a : Amounts p q d b) (w : Amounts p q e (!b))
    (t : Tagging p (Messenger q)) (h : rhyme a w) (hb : ∀ i,1≤q i)
    (hr : ∀ j:Bool,couple _ (funds w (transit (!b) (true,j)))=
      couple _ (funds w (transit (!b) (false,j))))
    (hg : 3≤p.g) (hodd : Odd p.g) (hj : 1≤p.J) : ∃ s,proclaims p a w t (reducedScript s) := by
  have ha {H : Type} [AddCommMonoid H] (i j : Nodes) (f : Messenger q→H) :
      ∑ x∈aiming (parcel b) (parcel (!b)) i j,f x=
        ∑ k:Fin (q (transit b (i,j))),f ⟨transit b (i,j),k⟩ := by
    have hA:=aim_sum b (transit b (i,j)) f
    have he:=(sendPair b (transit b (i,j))).trans (transit_inv b _)
    rw [show sendId b _=i from congrArg Prod.fst he,
      show sendId (!b) _=j from congrArg Prod.snd he] at hA
    exact hA
  apply choose_reduced_script p t _ _ _ _ (mailRole w) _ _ _ _ (tmill_sym ..) hg hodd hj
  · intro i
    rw [ha,ha,←funds_duos w,←funds_duos w]
    have hx:=hr i
    cases b <;> exact hx
  · intro i j
    rw [ha,sum_add_distrib,←funds_roles a,←funds_roles w]
    exact h _
  · intro i j
    let k:=transit b (i,j)
    let x:Messenger q:=⟨k,0,hb k⟩
    have he:=(sendPair b k).trans (transit_inv b (i,j))
    exact ⟨x,Finset.mem_filter.mpr ⟨mem_univ _,congrArg Prod.fst he,congrArg Prod.snd he⟩⟩

end
end Lax793645Proofs.Simplifications
