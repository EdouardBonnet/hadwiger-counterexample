import Lax793645Proofs.Simplifications.IndependentCorrections

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

namespace IndependentClub
variable {L I S X Y : Type} [DecidableEq L] [DecidableEq I] [Fintype S]
variable [AddCommGroup X] [Module F X] [Module.Finite F X]
variable [AddCommGroup Y] [Module F Y]

/-- The seven-generator bound survives the stronger selector independence
requirement. Span stability is needed after protecting up to four previous
directions; pairwise distinctness alone is not used. -/
theorem seven_list (C : Club I X L) (U : Bool → Space (Vec S)) (v : Bool → I → Vec S)
    (s : Straps L) (π : X →ₗ[F] Y) (V : Space X)
    (hspan : ∀ p : Finset I,p.card ≤ 4 →
      ration C (enlarge U v p) v s π=V ⊓ LinearMap.ker π)
    (hdim : dim (V ⊓ LinearMap.ker π : Space X) ≤ 2)
    (hchoose : ∀ y,∃ i,C.zone s i ∧ C.writes i∈V ∧ π (C.writes i)=y ∧
      ∀ b,(U b).mkQ (v b i) ≠ 0)
    (x : X) (hx : x∈V) :
    ∃ p : Finset I,bundle C U v p s ∧ C.contents p=x ∧ 1 ≤ p.card ∧ p.card ≤ 7 := by
  classical
  obtain ⟨i,hi,hV,hπ,hn⟩ := hchoose (π x)
  let p : Finset I := {i}
  have hp : bundle C U v p s := bundle_one C U v s hi hn
  have hsp (q : Finset I) (hq : q.card ≤ 3) :
      ration C (enlarge (enlarge U v p) v q) v s π=V ⊓ LinearMap.ker π := by
    rw [enlarge_union]
    apply hspan
    exact (Finset.card_union_le p q).trans (by simp only [p,Finset.card_singleton]; omega)
  have hcorr : x-C.writes i ∈ (V ⊓ LinearMap.ker π : Space X) := by
    refine ⟨V.sub_mem hx hV,?_⟩
    change π (x-C.writes i)=0
    rw [map_sub,hπ,sub_self]
  obtain ⟨q,hq,hQ,hs⟩ := jump_two C (enlarge U v p) v s π _ hsp hdim _ hcorr
  obtain ⟨hfull,hdis⟩ := bundle_combine C U v hp hq
  refine ⟨p∪q,hfull,?_,?_,?_⟩
  · rw [Club.contents,Finset.sum_union hdis]
    change C.contents p+C.contents q=x
    rw [hs]
    simp [p,Club.contents]
  · exact Finset.card_pos.mpr ⟨i,Finset.mem_union_left _ (by simp [p])⟩
  exact (Finset.card_union_le p q).trans (by simp only [p,Finset.card_singleton]; omega)

end IndependentClub
end
end Lax793645Proofs.Simplifications
