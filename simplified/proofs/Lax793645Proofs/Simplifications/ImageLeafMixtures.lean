import Lax793645Proofs.Simplifications.ClosedImagePartitions
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.WeightedPartitions

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A C I : Type} [Fintype A] [Fintype C] [Fintype I] [DecidableEq I] {N c : ℕ}

def imageDustPin : ImagePin C I N:=⟨⊥,0⟩

theorem image_dust_rank : imagePlanRank (imageDustPin (C:=C) (I:=I) (N:=N)).sp=0 := by
  simp [imageDustPin,imagePlanRank]

theorem image_dust_agree (X : A→C→Mat (Fin N) I) (x : A) :
    imagePinAgree X imageDustPin x := by
  intro e v hv
  have hv' : v=0:=hv
  rw [hv',Matrix.mulVec_zero,Matrix.mulVec_zero]

structure ImageRipe (X : A→C→Mat (Fin N) I) (cl : ImageClosure C I c)
    (w μ : Wgt A) (S : Finset A) (a : ImagePin C I N) (D ζ : ℝ) (K : ℕ) : Prop where
  pos : 0<partMass w S
  fixpin : ∀ x∈S,imagePinAgree X a x
  closed : cl.close a.sp=a.sp
  bound : imagePlanRank a.sp≤K
  clear : imagePinClear X a ζ (partW w S)
  density x : partW w S x≤bp (D*N)*μ x

structure ImageLeafMixture (A C I : Type) [Fintype C] [Fintype I] (N : ℕ) where
  T : Tiles A
  pin : Finset A→ImagePin C I N

namespace ImageLeafMixture
variable (s : ImageLeafMixture A C I N)

instance : Inhabited (ImageLeafMixture A C I N):=⟨⟨∅,fun _=>imageDustPin⟩⟩

def poller (x : A) : ImagePin C I N:=
  open scoped Classical in
  if h : inTiles s.T x then s.pin h.choose else imageDustPin
def rooting (x : A):=(s.poller x).sp
def amount (w : Wgt A):=allMass w s.T
def sap (w : Wgt A):=allW w s.T
def within (P : A→Prop):=∀ i∈s.T,∀ x∈i,P x

theorem poller_eq (h : apart s.T) {x i} (hi : i∈s.T) (hx : x∈i) : s.poller x=s.pin i := by
  classical
  have hc : inTiles s.T x:=⟨i,hi,hx⟩
  unfold poller
  rw [dif_pos hc,h _ _ hc.choose_spec.1 _ hi hc.choose_spec.2 hx]

structure strength (X : A→C→Mat (Fin N) I) (cl : ImageClosure C I c)
    (w μ : Wgt A) (D ζ : ℝ) (K : ℕ) : Prop where
  part : apart s.T
  leaf : ∀ i∈s.T,ImageRipe X cl w μ i (s.pin i) D ζ K

variable {s} {X : A→C→Mat (Fin N) I} {cl : ImageClosure C I c}
  {w μ : Wgt A} {D ζ : ℝ} {K : ℕ}

theorem root_bound (h : s.strength X cl w μ D ζ K) (x : A) :
    imagePlanRank (s.rooting x)≤K := by
  classical
  by_cases hx : inTiles s.T x
  · rw [rooting,poller,dif_pos hx]
    exact (h.leaf _ hx.choose_spec.1).bound
  rw [rooting,poller,dif_neg hx,image_dust_rank]
  exact Nat.zero_le K

theorem root_closed (h : s.strength X cl w μ D ζ K) (hbot : cl.close ⊥=⊥) (x : A) :
    cl.close (s.rooting x)=s.rooting x := by
  classical
  by_cases hx : inTiles s.T x
  · rw [rooting,poller,dif_pos hx]
    exact (h.leaf _ hx.choose_spec.1).closed
  rw [rooting,poller,dif_neg hx]
  exact hbot

theorem sap_law (h : 0<s.amount w) (hw : IsLaw w) : IsLaw (s.sap w):=on_law hw.nz h
theorem present {x : A} (h : s.sap w x≠0) : inTiles s.T x ∧ w x≠0:=onW_ne h
theorem in_parent {P : A→Prop} (h : s.within P) {x : A} (hx : inTiles s.T x) : P x:=
  h _ hx.choose_spec.1 _ hx.choose_spec.2
theorem upper_sap (hw : IsLaw w) (hp : 0<s.amount w) (x : A) :
    s.sap w x≤(s.amount w)⁻¹*w x:=on_mon hw.nz hp le_rfl x

/-- Initial leaves with stored closed pins, a joint density bound, and
spreading on every future exact-image test. -/
theorem first (X : A→C→Mat (Fin N) I) (hc : 1≤c) (cl : ImageClosure C I c)
    (hbot : cl.close ⊥=⊥) (ζ D : ℝ) (K : ℕ) (hz : 0<ζ) (hz' : ζ<1) (hn : 0<N)
    (hR : ∀ a : ImagePin C I N,cl.close a.sp=a.sp →
      pr μ (imagePinAgree X a)≤fee N ((ζ/c)/4) (imagePlanRank a.sp))
    (hcw : ∀ x,w x≤bp (D*N)*μ x) (hw : ∀ x,0≤w x) (P : A→Prop)
    (hK : D+ζ≤((ζ/c)-(ζ/c)/4)*K) :
    ∃ s : ImageLeafMixture A C I N,
      s.strength X cl w μ (D+K+1) ζ K ∧ s.within P ∧
        pr w P-bp (-ζ*N)≤s.amount w := by
  classical
  let R:=Finset.univ.filter P
  have hr (x : A) : x∈R↔P x:=by simp [R]
  obtain ⟨T,hT,hapart,herr⟩:=closed_image_partition X hc cl hz hz' hn hR hcw hw R
    imageDustPin hbot (fun x _=>image_dust_agree X x) hK
  choose a ha using (show ∀ S : Finset A,∃ a,S∈T →
    ClosedImageCell X cl w μ D ζ K S imageDustPin a from by
      intro S
      by_cases hs : S∈T
      · obtain ⟨a,ha⟩:=(hT S hs).2
        exact ⟨a,fun _=>ha⟩
      exact ⟨imageDustPin,fun h=>(hs h).elim⟩)
  let s : ImageLeafMixture A C I N:=⟨T,a⟩
  refine ⟨s,⟨hapart,fun i hi=>?_⟩,fun i hi x hx=>(hr x).mp ((hT i hi).1 hx),?_⟩
  · have hh:=ha i hi
    refine ⟨hh.pos,hh.fixpin,hh.closed,?_,hh.clear,hh.density⟩
    simpa only [image_dust_rank,zero_add] using hh.bound
  simp_rw [hr] at herr
  have hp (x : A) : P x → inTiles T x ∨ (P x ∧ ¬inTiles T x):=by tauto
  have hh:=((pr_mono hw hp).trans (pr_or_le hw)).trans (add_le_add_right herr (s.amount w))
  linarith only [hh]

end ImageLeafMixture
end
end Lax793645Proofs.Simplifications
