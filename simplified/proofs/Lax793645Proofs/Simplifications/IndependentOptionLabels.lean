import Lax793645Proofs.Simplifications.IndependentScalarSupply
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FiniteOptionLabels

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis StatusAnalysis.Guild
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section

variable {r : ℕ} {d e : Rates}

set_option maxHeartbeats 1000000 in
/-- Enumeration as a numerical option preserves the full selector
independence, not only distinctness of the labels. -/
theorem independent_invite (p : Shape) (u : Terrain p r)
    (s : Gazette p r d) (t : Gazette p r e) (A B : Stalls p) (η : ℝ)
    (U : Bool → Space (Vec (SelIdx p.b p.j))) (v : ∀ i,Suite d e i)
    (H : Straps (Label p.b)) (f : Bags (Scriptum p d e))
    (hf : IndependentParade (stellar u s t η A B) U H v f Finset.univ) :
    let C := stellar u s t η A B
    ∃ (q : Volumes) (g : Engagement p (toFormat q) d e),
      (∀ i,1 ≤ toFormat q i ∧ toFormat q i ≤ 7) ∧
      (∀ i : Messenger (toFormat q),(C i.1).valid (g i)) ∧
      (∀ side : Bool,LinearIndependent F
        ((U side).mkQ ∘ fun i : Messenger (toFormat q) => selV p.j ((g i).1.s side))) ∧
      ∀ i,∑ j : Fin (toFormat q i),(C i).writes (g ⟨i,j⟩)=v i := by
  classical
  intro C
  have he i := hf.batch i (mem_univ _)
  let q (i : Grid) : Fin 8 := ⟨(f i).card,Nat.lt_succ_of_le (he i).2.2.2⟩
  let Q := toFormat q
  let E (i : Grid) : Fin (Q i) ≃ (↑(f i) : Type) :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe _)).symm
  let g : Engagement p Q d e := fun i => (E _ i.2).val
  have hG i : g i ∈ f i.1 := (E i.1 i.2).property
  let embed (i : Messenger Q) :
      (Finset.univ.sigma f : Set (Σ k,Scriptum p d e k)) :=
    ⟨⟨i.1,g i⟩,Finset.mem_sigma.mpr ⟨Finset.mem_univ _,hG i⟩⟩
  have hinj : Injective embed := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij : i=j := congrArg (fun z => z.val.1) h
    subst j
    have hval : (E i x).val=(E i y).val :=
      eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2
    have hxy : x=y := (E i).injective (Subtype.ext hval)
    subst y
    rfl
  refine ⟨q,g,fun i => (he i).2.2,fun i => ((he _).1.1 _ (hG i)).1,
    fun side => ?_,fun i => ?_⟩
  · exact (hf.independent side).comp embed hinj
  calc _ = ∑ x : ↑(f i),(C i).writes x.val :=
          Equiv.sum_comp (E i) (fun x => (C i).writes x.val)
       _ = _ := (Finset.sum_coe_sort (f i) _).trans (he i).2.1

end
end Lax793645Proofs.Simplifications
