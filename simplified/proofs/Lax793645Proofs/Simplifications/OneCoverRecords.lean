import Lax793645Proofs.Simplifications.OneEffectiveSpaces
import Lax793645Proofs.Simplifications.OnePhaseAlternativeSupport
import Lax793645Proofs.Simplifications.OneSymmetricOffsets
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FourPhaseBits

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ}

def oneCoverDelta (T : Cov p (2*N)) (Δ : OneUnit p n N→Ambient p (2*N))
    (x : OneUnit p n N) : coverX p T :=
  open scoped Classical in
  if h : covered p T (Δ x) then ⟨_,h⟩ else 0

def oneJuris (T : Cov p (2*N)) (x : OneUnit p n N) (S : Party) :
    Module.Dual F (coverX p T) :=
  (joinPhase p (oneListens x) S).comp (coverX p T).subtype

def oneDaypair (T : Cov p (2*N)) (Δ : OneUnit p n N→Ambient p (2*N))
    (x : OneUnit p n N) : Daypair p T :=
  (oneCoverDelta T Δ x,fun i=>oneJuris T x (unary i))

abbrev OneEffSeq (a : ImagePlan (Comp p.g) (OneColumn p n)) :=
  ∀ i : Bool,oneEffectivePins (oneEndpointPrimalPins a) i

def oneEntrySeq (a : ImagePlan (Comp p.g) (OneColumn p n))
    (marks : Bool→Profile p n) : OneEffSeq a :=
  open scoped Classical in
  fun i=>if h : marks i∈oneEffectivePins (oneEndpointPrimalPins a) i then ⟨_,h⟩ else 0

abbrev OneStory (T : Cov p (2*N)) (a : ImagePlan (Comp p.g) (OneColumn p n)) :=
  Daypair p T × OneEffSeq a

instance oneStoryFintype (T : Cov p (2*N)) (a : ImagePlan (Comp p.g) (OneColumn p n)) :
    Fintype (OneStory T a) := by
  classical
  letI : Fintype (Module.Dual F (coverX p T)):=Fintype.ofInjective
    (fun f=>(f : coverX p T→F)) DFunLike.coe_injective
  letI : ∀ i,Fintype (oneEffectivePins (oneEndpointPrimalPins a) i):=fun _=>Fintype.ofFinite _
  exact inferInstanceAs (Fintype (Daypair p T × OneEffSeq a))

def oneStory (T : Cov p (2*N)) (a : ImagePlan (Comp p.g) (OneColumn p n))
    (marks : OneUnit p n N→Bool→Profile p n) (x : OneUnit p n N) : OneStory T a :=
  (oneDaypair T (fun x=>oneMarkedDelta x (marks x)) x,oneEntrySeq a (marks x))

def oneSpecialLeaf (T : Cov p (2*N)) (marks : OneUnit p n N→Bool→Profile p n)
    (a : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (S : Finset (OneUnit p n N))
    (b : ImagePin (Comp p.g) (OneColumn p n) (2*N)) : Prop :=
  a.sp≤b.sp ∧ ∀ x∈S,∀ y∈S,
    marks x=marks y ∧ oneMarkedDelta x (marks x)=oneMarkedDelta y (marks y) ∧
      ∀ i,oneJuris T x (unary i)=oneJuris T y (unary i)

/-- Since the old pins already split into coordinate blocks, recording
the marks and phase restrictions needs no additional projected pins. -/
theorem one_story_ok (T : Cov p (2*N)) (marks : OneUnit p n N→Bool→Profile p n)
    (a : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (S : Finset (OneUnit p n N))
    (h : ∀ x∈S,imagePinAgree oneCoordinateImages a x ∧
      covered p T (oneMarkedDelta x (marks x)) ∧
      ∀ i,marks x i∈oneEffectivePins (oneEndpointPrimalPins a.sp) i)
    (v : OneStory T a.sp)
    (b : ImagePin (Comp p.g) (OneColumn p n) (2*N)) (G : Finset (OneUnit p n N))
    (hG : ∀ x∈G,x∈S ∧ oneStory T a.sp marks x=v) (hab : a.sp≤b.sp) :
    oneSpecialLeaf T marks a G b := by
  classical
  refine ⟨hab,fun x hx y hy=>?_⟩
  have he:=(hG x hx).2.trans (hG y hy).2.symm
  have hd (z) (hz : z∈G) : (oneStory T a.sp marks z).1.1.val=oneMarkedDelta z (marks z) := by
    simp only [oneStory,oneDaypair,oneCoverDelta,dif_pos ((h z (hG z hz).1).2.1)]
  have hm (z) (hz : z∈G) (i : Bool) : ((oneStory T a.sp marks z).2 i).val=marks z i := by
    simp only [oneStory,oneEntrySeq,dif_pos ((h z (hG z hz).1).2.2 i)]
  refine ⟨funext (fun i=>?_ ),?_,fun i=>?_⟩
  · rw [←hm x hx i,←hm y hy i,he]
  · rw [←hd x hx,←hd y hy,he]
  exact congrFun (congrArg (fun z : OneStory T a.sp=>z.1.2) he) i

theorem one_story_size (T : Cov p (2*N)) (a : ImagePlan (Comp p.g) (OneColumn p n))
    (K d : ℕ) (hK : imagePlanRank a≤K) (hd : cdim p T≤d) :
    num (OneStory T a)≤bp ((3*d:ℝ)*(2*N)+2*K^2) := by
  classical
  have h1 : dim (coverX p T)≤(2*N)*d :=
    (cover_dim p T).trans (Nat.mul_le_mul_left _ hd)
  have h2 : dim (Daypair p T)≤3*d*(2*N) := by
    unfold Daypair dim
    rw [finrank_prod,finrank_pi_fintype,Fintype.sum_bool,Subspace.dual_finrank_eq]
    change dim _+(dim _+dim _)≤_
    nlinarith only [h1]
  have h3 : dim (OneEffSeq a)≤2*K^2 := by
    unfold OneEffSeq dim
    rw [finrank_pi_fintype,Fintype.sum_bool,two_mul]
    have hh (i : Bool) : dim (oneEffectivePins (oneEndpointPrimalPins a) i)≤K^2 :=
      (one_effective_dimension a i).trans (by gcongr)
    exact add_le_add (hh _) (hh _)
  unfold num
  rw [card_space]
  apply bp_le
  have hh : dim (OneStory T a)≤3*d*(2*N)+2*K^2 := by
    unfold OneStory dim
    rw [finrank_prod]
    exact add_le_add h2 h3
  exact_mod_cast hh

def oneQuench (Δ : OneUnit p n N→Ambient p (2*N))
    (x : OneUnit p n N×OneUnit p n N) : Quad :=
  (fun i=>joinPhase p (oneListens x.2) (unary i) (Δ x.1),
   fun i=>joinPhase p (oneListens x.1) (unary i) (Δ x.2))

theorem one_phase_fixed (T : Cov p (2*N)) (marks : OneUnit p n N→Bool→Profile p n)
    {a b a' b' : ImagePin (Comp p.g) (OneColumn p n) (2*N)}
    {S R : Finset (OneUnit p n N)} {x x' y y' : OneUnit p n N}
    (hS : oneSpecialLeaf T marks a S a') (hR : oneSpecialLeaf T marks b R b')
    (hx : x∈S) (hx' : x'∈S) (hy : y∈R) (hy' : y'∈R)
    (hC : covered p T (oneMarkedDelta x (marks x)))
    (hC' : covered p T (oneMarkedDelta y (marks y))) :
    oneQuench (fun z=>oneMarkedDelta z (marks z)) (x,y)=
      oneQuench (fun z=>oneMarkedDelta z (marks z)) (x',y') := by
  obtain ⟨_,hdx,hjx⟩:=hS.2 x hx x' hx'
  obtain ⟨_,hdy,hjy⟩:=hR.2 y hy y' hy'
  unfold oneQuench
  dsimp only
  rw [←hdx,←hdy]
  exact Prod.ext
    (funext fun i=>LinearMap.congr_fun (hjy i) (⟨_,hC⟩ : coverX p T))
    (funext fun i=>LinearMap.congr_fun (hjx i) (⟨_,hC'⟩ : coverX p T))

end
end Lax793645Proofs.Simplifications
