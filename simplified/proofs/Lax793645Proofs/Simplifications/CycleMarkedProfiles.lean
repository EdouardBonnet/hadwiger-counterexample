import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.TensorIntersections
import Lax793645Proofs.Simplifications.CycleIntrinsic

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Finset LinearMap
open scoped BigOperators
noncomputable section

variable {p : Shape} {n : ℕ}

def bitSupport {g : ℕ} (t : Fin g → F) : Finset (Fin g) :=
  Finset.univ.filter (fun l => t l≠0)

def asBits {g : ℕ} (t : Fin g → F) : Fin g → Bool := fun l => decide (t l=1)

theorem bits_roundtrip {g : ℕ} (t : Fin g → F) (l : Fin g) :
    boolBit (asBits t l)=t l := by
  rcases bit_cases (t l) with h|h <;> simp [asBits,boolBit,h]

theorem boolBit_injective : Function.Injective boolBit := by
  intro a b h
  cases a <;> cases b <;> simp [boolBit] at h ⊢

theorem bitSupport_asBits {g : ℕ} (t : Fin g → F) : ones (asBits t)=bitSupport t := by
  classical
  ext l
  rcases bit_cases (t l) with h|h <;> simp [ones,asBits,bitSupport,h]

def normalBits {g : ℕ} (t : Fin g → F) : Fin g → F :=
  fun l => boolBit (normalizeTrace (asBits t) l)

theorem normalBits_majority {g : ℕ} (hg : Odd g) (t : Fin g → F) :
    2*(bitSupport (normalBits t)).card<g := by
  have hm := normalized_majority (asBits t) (by simpa using hg)
  have he : bitSupport (normalBits t)=ones (normalizeTrace (asBits t)) := by
    classical
    ext l
    cases h : normalizeTrace (asBits t) l <;> simp [bitSupport,normalBits,ones,h,boolBit]
  rw [he]
  simpa only [majorityZero,Fintype.card_fin] using hm

theorem boolBit_complement (b : Bool) : boolBit (!b)=boolBit b+1 := by
  cases b <;> simp [boolBit,CharTwo.add_self_eq_zero]

theorem normalBits_pair {g : ℕ} (t : Fin g → F) (i j : Fin g) :
    normalBits t i+normalBits t j=t i+t j := by
  unfold normalBits normalizeTrace
  split_ifs
  · simp only [bits_roundtrip]
  · simp only [complement,boolBit_complement,bits_roundtrip]
    calc
      _ = (t i+t j)+(1+1) := by abel
      _ = _ := by rw [char_two,add_zero]

/-- Majority-zero trace vectors are determined by their cycle differences. -/
theorem majority_trace_unique {g : ℕ} (hg : Odd g) (h3 : 3≤g)
    (s t : Fin g → F) (hs : 2*(bitSupport s).card<g) (ht : 2*(bitSupport t).card<g)
    (he : ∀ e : CycleGeometry.Comp g,CycleGeometry.cut s e=CycleGeometry.cut t e) : s=t := by
  obtain ⟨r,hr⟩ := hg
  have heq : g=2*r+1 := by omega
  subst g
  have hs' : majorityZero (asBits s) := by
    unfold majorityZero; rw [bitSupport_asBits,Fintype.card_fin]; exact hs
  have ht' : majorityZero (asBits t) := by
    unfold majorityZero; rw [bitSupport_asBits,Fintype.card_fin]; exact ht
  have hb : asBits s=asBits t := normalized_edge_trace_unique _ _ hs' ht' (by
    intro i
    apply boolBit_injective
    rw [boolBit_xor,boolBit_xor,bits_roundtrip,bits_roundtrip,bits_roundtrip,bits_roundtrip]
    have hx := he (CycleGeometry.forward (by omega : 2≤2*r+1) i.castSucc)
    rw [CycleGeometry.cut_forward,CycleGeometry.cut_forward] at hx
    have hn : CycleGeometry.next i.castSucc=i.succ := by
      apply Fin.ext
      simp only [CycleGeometry.next,Fin.val_castSucc,Fin.val_succ]
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
    rwa [hn] at hx)
  funext l
  have hh := congrArg boolBit (congrFun hb l)
  simpa only [bits_roundtrip] using hh

/-- The normalized object is a vector of bits, not a matrix representative. -/
theorem exists_majority_trace (x : Profile p n) (hx : x ∈ Xspace p n) (hg : Odd p.g) :
    ∃ t : Tag p.g → F, 2*(bitSupport t).card<p.g ∧
      ∀ e,eta p n (x e)=CycleGeometry.cut t e := by
  obtain ⟨w,hw,rfl⟩ := mem_X.mp hx
  let t := fun l => eta p n (w l)
  refine ⟨normalBits t,normalBits_majority hg t,fun e => ?_⟩
  change eta p n (w e.val.1+w e.val.2)=normalBits t e.val.1+normalBits t e.val.2
  rw [normalBits_pair,map_add]

/-- Read just the ordinary testers owned by the outgoing tag. -/
def ordinaryBit (p : Shape) (n : ℕ) (x : Profile p n) (l : Tag p.g) : F :=
  ∑ t : Tag p.g,etab p n (Block.O l t) (CycleGeometry.outgoingMap l x)

theorem ordinaryBit_cut (w : Tag p.g → Moment p n) (hw : ∀ l,w l∈Wtag p n l)
    (l : Tag p.g) : ordinaryBit p n (cut p n w) l=etaO p n (w l) := by
  classical
  have hn : ¬allowed l (CycleGeometry.next l) := by
    intro h
    exact (CycleGeometry.adjacent_next h.1 l).ne h.2
  change (∑ t,etab p n (Block.O l t) (CycleGeometry.outgoingMap l (CycleGeometry.cut w)))=_
  simp only [CycleGeometry.outgoingMap_cut,map_add,
    etab_disabled p hn _ (hw (CycleGeometry.next l)),add_zero]
  unfold etaO
  simp only [LinearMap.sum_apply]
  symm
  apply Finset.sum_eq_single l
  · intro d _ hd
    exact Finset.sum_eq_zero (fun t _ => etab_disabled p (fun h => hd h.2) t (hw l))
  · simp

theorem etaO_components (x : Profile p n) (hx : x ∈ Xspace p n) (e : Comp p.g) :
    etaO p n (x e)=ordinaryBit p n x e.val.1+ordinaryBit p n x e.val.2 := by
  obtain ⟨w,hw,rfl⟩ := mem_X.mp hx
  rw [ordinaryBit_cut w hw,ordinaryBit_cut w hw]
  change etaO p n (w _+w _)=_
  exact map_add _ _ _

theorem ordinaryBit_support (hg : 3≤p.g) (x : Profile p n) :
    (bitSupport (ordinaryBit p n x)).card≤totalRank x := by
  classical
  rw [bitSupport,Finset.card_eq_sum_ones,Finset.sum_filter]
  calc
    _ ≤ ∑ l : Tag p.g,(x (CycleGeometry.forward (by omega : 2≤p.g) l)).rank := by
      apply Finset.sum_le_sum
      intro l _
      split_ifs with h
      · apply matrix_nonzero_rank
        intro hz
        apply h
        unfold ordinaryBit CycleGeometry.outgoingMap
        rw [dif_pos (by omega : 2≤p.g)]
        simp only [LinearMap.proj_apply,hz,map_zero,Finset.sum_const_zero]
      · exact Nat.zero_le _
    _ = totalRank x := Equiv.sum_comp (CycleGeometry.forwardEquiv hg) (fun e => (x e).rank)

theorem map_outgoing (f : Moment p n →ₗ[F] F) (x : Profile p n) (l : Tag p.g) :
    f (CycleGeometry.outgoingMap l x)=CycleGeometry.outgoingMap l (fun e => f (x e)) := by
  unfold CycleGeometry.outgoingMap
  split_ifs <;> simp

theorem map_matching (f : Moment p n →ₗ[F] F) (x : Profile p n) (l : Tag p.g) :
    f (CycleGeometry.matchingMap l x)=CycleGeometry.matchingMap l (fun e => f (x e)) := by
  simp only [CycleGeometry.matchingMap,LinearMap.sum_apply,map_sum,map_outgoing]

theorem intrinsic_tester (x : Profile p n) (hx : x∈Xspace p n) (hg : Odd p.g)
    (t : Tag p.g → F) (ht : ∀ e,eta p n (x e)=CycleGeometry.cut t e) (l : Tag p.g) :
    role p n x+sharedT p n l x=(∑ i,t i)+(t l+ordinaryBit p n x l) := by
  classical
  let o := ordinaryBit p n x
  let s := fun l => t l+o l
  have hs : (fun e => etab p n Block.S (x e))=CycleGeometry.cut s := by
    funext e
    have he := ht e
    rw [eta,LinearMap.add_apply,etaO_components x hx] at he
    change (o e.val.1+o e.val.2)+etab p n Block.S (x e)=t e.val.1+t e.val.2 at he
    change _=(t e.val.1+o e.val.1)+(t e.val.2+o e.val.2)
    calc
      _ = (o e.val.1+o e.val.2)+((o e.val.1+o e.val.2)+etab p n Block.S (x e)) := by
        rw [←add_assoc,char_two,zero_add]
      _ = _ := by rw [he]; abel
  have ha : role p n x=∑ i,o i := by
    simp only [role,roleT,LinearMap.sum_apply,LinearMap.comp_apply,o,ordinaryBit]
    exact Finset.sum_comm
  have hb : sharedT p n l x=(∑ i,s i)+s l := by
    change etab p n Block.S (CycleGeometry.matchingMap l x)=_
    rw [map_matching,hs,CycleGeometry.matchingMap_cut hg]
  rw [ha,hb]
  simp only [s,Finset.sum_add_distrib]
  calc
    _ = ((∑ i,t i)+(t l+o l))+((∑ i,o i)+(∑ i,o i)) := by abel
    _ = _ := by rw [char_two,add_zero]

theorem sharedBit_support (hg : Odd p.g) (h3 : 3≤p.g) (D : ℕ) (x : Profile p n)
    (t : Tag p.g → F) (ht : 2*(bitSupport t).card<p.g) (hr : totalRank x≤2*D) :
    (bitSupport (fun l => t l+ordinaryBit p n x l)).card≤(p.g-1)/2+2*D := by
  classical
  have hs : bitSupport (fun l => t l+ordinaryBit p n x l) ⊆
      bitSupport t ∪ bitSupport (ordinaryBit p n x) := by
    intro l hl
    simp only [bitSupport,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at hl ⊢
    by_contra! h
    exact hl (by rw [h.1,h.2,add_zero])
  have hcard := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have ho := (ordinaryBit_support h3 x).trans hr
  omega

end
end Lax793645Proofs.Simplifications
