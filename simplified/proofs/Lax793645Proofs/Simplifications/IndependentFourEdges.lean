import Lax793645Proofs.Simplifications.IndependentCertificates
import Lax793645Proofs.Simplifications.ScalableSpanStability
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FourEdgeFamilies

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

namespace IndependentClub
variable {T S : Type} [DecidableEq T] [Fintype S]

theorem independent_union_over_span (U : Bool → Space (Vec S)) (v : Bool → T → Vec S)
    (p q : Finset T)
    (hp : ∀ side,LinearIndepOn F ((U side).mkQ ∘ v side) (p : Set T))
    (hq : ∀ side,LinearIndepOn F ((enlarge U v p side).mkQ ∘ v side) (q : Set T)) :
    ∀ side,LinearIndepOn F ((U side).mkQ ∘ v side) ((p∪q) : Set T) := by
  let C : Club T F Unit := ⟨fun _ => True,fun _ => 0,fun _ _ => ()⟩
  have hzone (i : T) : C.zone ⊥ i := by simp [C,Club.zone]
  simpa only [Finset.coe_union] using
    (bundle_combine C U v ⟨fun i _ => hzone i,hp⟩ ⟨fun i _ => hzone i,hq⟩).1.2

end IndependentClub

variable {I : Grid → Type} [∀ i,DecidableEq (I i)] {A B : Rates} {b j : ℕ}
open IndependentClub StatusAnalysis.Guild

def congressDirections (C : Congress I A B (Label b)) (side : Bool) (k : Σ i,I i) :=
  selV j ((C k.1).addr k.2 side)

structure IndependentParade (C : Congress I A B (Label b))
    (U : Bool → Space (Vec (SelIdx b j))) (s : Straps (Label b))
    (target : ∀ i,Suite A B i) (g : Bags I) (p : Finset Grid) : Prop where
  batch (i) (h : i∈p) : (C i).bundle (g i) s ∧
    (C i).contents (g i)=target i ∧ 1 ≤ (g i).card ∧ (g i).card ≤ 7
  independent : ∀ side,LinearIndepOn F ((U side).mkQ ∘ congressDirections C side)
    (p.sigma g : Set (Σ i,I i))

theorem independent_bundle_ordinary {T X : Type}
    [DecidableEq T] [AddCommGroup X] [Module F X] (C : Club T X (Label b))
    (U : Bool → Space (Vec (SelIdx b j))) (s : Straps (Label b)) (p : Finset T)
    (h : IndependentClub.bundle C U (labelDirections C) p s) : C.bundle p s := by
  refine ⟨h.1,fun side x hx y hy he => ?_⟩
  apply (h.2 side).injOn hx hy
  change C.addr x side=C.addr y side at he
  change (U side).mkQ (selV j (C.addr x side))=(U side).mkQ (selV j (C.addr y side))
  rw [he]

set_option maxHeartbeats 1200000 in
/-- Assemble the four scalar certificates while protecting every selector
chosen on earlier edges. -/
theorem independent_full_parade (C : Congress I A B (Label b))
    (U : Bool → Space (Vec (SelIdx b j))) (s : Straps (Label b))
    (target : ∀ i,Suite A B i)
    (hselect : ∀ P : Finset (Σ i,I i),P.card ≤ 28 → ∀ i : Grid,
      ∃ q : Finset (I i),
        IndependentClub.bundle (C i) (enlarge U (congressDirections C) P) (labelDirections (C i)) q s ∧
        (C i).contents q=target i ∧ 1 ≤ q.card ∧ q.card ≤ 7) :
    ∃ g,IndependentParade C U s target g Finset.univ := by
  classical
  have hstep (p : Finset Grid) : ∃ g,IndependentParade C U s target g p := by
    induction p using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => ∅,⟨fun i hi => (Finset.notMem_empty i hi).elim,?_⟩⟩
      intro side
      simp
    | insert i p hi ih =>
      obtain ⟨g,hg⟩ := ih
      let P := p.sigma g
      have hcard : P.card ≤ 28 := by
        rw [Finset.card_sigma]
        have hh := Finset.sum_le_sum (fun k hk => (hg.batch k hk).2.2.2)
        have hc : p.card ≤ 4 := p.card_le_univ.trans_eq (by simp [Grid,Nodes])
        simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at hh
        omega
      obtain ⟨q,hq,hcontents,hpos,hseven⟩ := hselect P hcard i
      let f := Function.update g i q
      let emb : I i ↪ (Σ k,I k) :=
        ⟨Sigma.mk i,fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
      let Q := q.map emb
      have hnew : ∀ side,LinearIndepOn F
          ((enlarge U (congressDirections C) P side).mkQ ∘ congressDirections C side)
          (Q : Set (Σ k,I k)) := by
        intro side
        rw [Finset.coe_map]
        exact (hq.2 side).image_of_comp (Sigma.mk i) _
      have heq : (insert i p).sigma f=P∪Q := by
        ext k
        rcases k with ⟨k,x⟩
        simp only [Finset.mem_sigma,Finset.mem_insert,Finset.mem_union,P,Q,Finset.mem_map]
        by_cases hk : k=i
        · subst k
          simp [f,hi,emb,Function.Embedding.coeFn_mk]
          constructor
          · intro hx
            exact ⟨x,hx,rfl⟩
          · rintro ⟨a,ha,he⟩
            have hax : a=x := eq_of_heq (Sigma.mk.inj_iff.mp he).2
            simpa [hax] using ha
        simp [f,hk,Ne.symm hk,emb,Function.Embedding.coeFn_mk]
        intro a ha he
        have hik : i=k := congrArg Sigma.fst he
        exact (hk hik.symm).elim
      refine ⟨f,⟨fun k hk => ?_,?_⟩⟩
      · rcases Finset.mem_insert.mp hk with hki|hk
        · subst k
          unfold f
          rw [Function.update_self]
          exact ⟨independent_bundle_ordinary _ _ _ _ hq,hcontents,hpos,hseven⟩
        unfold f
        rw [Function.update_of_ne (show k ≠ i from fun he => hi (he ▸ hk))]
        exact hg.batch k hk
      rw [heq]
      simpa only [Finset.coe_union] using
        independent_union_over_span U (congressDirections C) P Q hg.independent hnew
  exact hstep _

theorem independent_parade_ordinary (C : Congress I A B (Label b))
    (U : Bool → Space (Vec (SelIdx b j))) (s : Straps (Label b))
    (target : ∀ i,Suite A B i) (g : Bags I) (p : Finset Grid)
    (h : IndependentParade C U s target g p) : Parade C s target g p := by
  refine ⟨h.batch,?_⟩
  intro i k hi hk hne x hx y hy side he
  have hx' : (⟨i,x⟩ : Σ k,I k) ∈ p.sigma g := Finset.mem_sigma.mpr ⟨hi,hx⟩
  have hy' : (⟨k,y⟩ : Σ k,I k) ∈ p.sigma g := Finset.mem_sigma.mpr ⟨hk,hy⟩
  have hvec : ((U side).mkQ ∘ congressDirections C side) ⟨i,x⟩=
      ((U side).mkQ ∘ congressDirections C side) ⟨k,y⟩ := by
    change (U side).mkQ (selV j ((C i).addr x side))=(U side).mkQ (selV j ((C k).addr y side))
    rw [he]
  exact hne (congrArg Sigma.fst ((h.independent side).injOn hx' hy' hvec))

end
end Lax793645Proofs.Simplifications
