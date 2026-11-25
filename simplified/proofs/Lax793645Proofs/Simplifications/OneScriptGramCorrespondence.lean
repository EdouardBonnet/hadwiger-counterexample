import Lax793645Proofs.Simplifications.OneKeyGramConditions
import Lax793645Proofs.Simplifications.OneBinaryQueryTests

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module Function Finset
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def oneKnows (v : Template p I) (s : Script p I) (m : Mixer p n)
    (z : Inputs p n I) (a b : I) : Prop :=
  v.aim a=v.aim b→
    (∀ i : ReducedOne p,s a b (reducedSlot i)=
      evmat (reducedOrdered m i) (v.croon a (z a)) (v.croon b (z b))) ∧
    (∀ i : ReducedOne p,s b a (reducedSlot i)=
      evmat (reducedOrdered m i) (v.croon b (z b)) (v.croon a (z a)))

theorem one_knows_rev (v : Template p I) (s : Script p I) (m : Mixer p n)
    (z : Inputs p n I) {a b : I} (h : oneKnows v s m z a b) :
    oneKnows v s m z b a:=fun he=>(h he.symm).symm

theorem one_voice_agreement (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : OneUnit p n N) (z : Inputs p n I) (hw : ∀ i,oneFrameLaw m (x i)) (j : v.Chorus) :
    listen v.choral (oneChime v m x) z j=oneLyrics v s j ↔
      oneVerges v.t (oneVolleyKeys (v.draw z) v.t x) (v.verses j).1 (v.verses j).2 ∧
        oneKnows v s m z (v.verses j).1 (v.verses j).2 := by
  let y:=oneVolleyKeys (v.draw z) v.t x
  cases j with
  | inr k=>
    let a:=k.val.1
    let b:=k.val.2
    have he : v.aim a≠v.aim b:=by rw [k.property.1,k.property.2]; decide
    have hh e ha hb :
        listen v.choral (oneChime v m x) z (.inr k) (⟨e,ha,hb⟩ : OneCrossing p (v.t a) (v.t b))=
          oneKeyVoice v.t y a b e ha hb := by
      change evmat (oneDuel (x true e) (x false e)) _ _=_
      rw [one_voice_note,k.property.1,k.property.2]
      rfl
    constructor
    · intro h
      exact ⟨fun e ha hb=>(hh e ha hb).symm.trans (congrFun h _),fun ht=>(he ht).elim⟩
    rintro ⟨h,_⟩
    funext e
    exact (hh e.val e.property.1 e.property.2).trans (h e.val e.property.1 e.property.2)
  | inl k=>
    let a:=k.val.1
    let b:=k.val.2
    have he : v.aim a=v.aim b:=k.property.1
    let u:=listen v.choral (oneChime v m x) z (.inl k)
    let d:=oneLyrics v s (.inl k)
    have hi1 i : u (.inl (i,true))=d (.inl (i,true)) ↔
        s a b (reducedSlot i)=evmat (reducedOrdered m i) (v.croon a (z a)) (v.croon b (z b)):=Eq.comm
    have hi2 i : u (.inl (i,false))=d (.inl (i,false)) ↔
        s b a (reducedSlot i)=evmat (reducedOrdered m i) (v.croon b (z b)) (v.croon a (z a)) := by
      change evmat (reducedOrdered m i)ᵀ _ _=s b a (reducedSlot i) ↔ _
      rw [evmat_transpose]
      exact Eq.comm
    have ht e ha hb : u (.inr ⟨(),⟨e,ha,hb⟩⟩)=d (.inr ⟨(),⟨e,ha,hb⟩⟩) ↔
        oneKeyVoice v.t y a b e ha hb=0 := by
      rw [one_voice_same v x z m hw e a b ha hb he]
      rfl
    change u=d ↔ oneVerges v.t y a b ∧oneKnows v s m z a b
    constructor
    · intro h
      exact ⟨fun e ha hb=>(ht e ha hb).mp (congrFun h _),
        fun _=>⟨fun i=>(hi1 i).mp (congrFun h _),fun i=>(hi2 i).mp (congrFun h _)⟩⟩
    rintro ⟨h₁,h₂⟩
    specialize h₂ he
    funext j
    rcases j with ⟨i,_|_⟩|j
    · exact (hi2 i).mpr (h₂.2 i)
    · exact (hi1 i).mpr (h₂.1 i)
    obtain ⟨e,ha,hb⟩:=j.property
    have hj : j=⟨(),⟨e,ha,hb⟩⟩:=Subsingleton.elim _ _
    rw [hj]
    exact (ht e ha hb).mpr (h₁ e ha hb)

theorem one_neigh_voice (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : OneUnit p n N) (z : Inputs p n I) (hw : ∀ i,oneFrameLaw m (x i)) (hm : ReducedMixerLaw m) :
    onePerforms v s m x z ↔(v.draw z).reads (reducedScript s) m ∧
      ∀ i j,i≠j→ oneVerges v.t (oneVolleyKeys (v.draw z) v.t x) i j := by
  let y:=oneVolleyKeys (v.draw z) v.t x
  let g i j:=oneVerges v.t y i j ∧oneKnows v s m z i j
  have h₁ : onePerforms v s m x z ↔∀ i j,i≠j→ g i j := by
    unfold onePerforms
    rw [funext_iff]
    simp_rw [one_voice_agreement v s m x z hw]
    change (∀ i,g (v.verses i).1 (v.verses i).2) ↔ _
    constructor
    · intro h i j hij
      obtain ⟨k,hk|hk⟩:=Template.across_duet v hij
      · specialize h k
        rwa [hk] at h
      specialize h k
      rw [hk] at h
      exact ⟨one_verges_rev v.t y h.1,one_knows_rev v s m z h.2⟩
    exact fun h i=>h _ _ (v.choral.diff i)
  rw [h₁,reduced_reads_iff (v.draw z) s m hm]
  constructor
  · intro h
    exact ⟨fun i j hij he=>((h i j hij).2 he).1,fun i j hij=>(h i j hij).1⟩
  rintro ⟨h,h'⟩ i j hij
  exact ⟨h' i j hij,fun he=>⟨h i j hij he,h j i (Ne.symm hij) he.symm⟩⟩

/-- The single-frame binary status asks exactly for the nominal mixer
prescriptions and the quadratic reference equations. -/
theorem one_performs_own (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : OneUnit p n N) (z : Inputs p n I) (hw : ∀ i,oneFrameLaw m (x i))
    (hm : ReducedMixerLaw m) (hj : 1≤p.j) (q : I→F) (hq : ∀ i,dialed p (v.t i) (v.f i) (z i)=q i) :
    onePerforms v s m x z ↔(v.draw z).reads (reducedScript s) m ∧
      oneOwnKeyPart v.t q (oneVolleyKeys (v.draw z) v.t x) := by
  rw [one_neigh_voice v s m x z hw hm,one_own_key_part]
  apply and_congr Iff.rfl
  have ht (i : I):=one_voices_diag v m x z hw hj i
  simp_rw [hq] at ht
  exact ⟨fun h=>⟨ht,h⟩,fun h=>h.2⟩

theorem one_performs_coordinates (v : Template p I) (s : Script p I) (m : Mixer p n)
    (x : OneUnit p n N) (z : Inputs p n I) (hw : ∀ i,oneFrameLaw m (x i))
    (hm : ReducedMixerLaw m) (hj : 1≤p.j) (q : I→F) (hq : ∀ i,dialed p (v.t i) (v.f i) (z i)=q i) :
    onePerforms v s m x z ↔(v.draw z).reads (reducedScript s) m ∧
      oneOwnPart v.t q (oneTemplateCoordinates v x z) := by
  rw [one_performs_own v s m x z hw hm hj q hq]
  rfl

end
end Lax793645Proofs.Simplifications
