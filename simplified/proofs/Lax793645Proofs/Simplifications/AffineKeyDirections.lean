import Lax793645Proofs.Simplifications.ProtectedTensorAnnihilators
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.FrozenProjections

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap
open scoped BigOperators
noncomputable section

variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]

abbrev CallsAt (v : Volley p n I) (i : Bool) := {j : I // j ∈ v.here i}

/-- Protection now concerns actual independent point families, not all
families of distinct labels. The cutoff applies to reshaped pin vectors. -/
def affineAvoids (v : Volley p n I) (a : Plan p n) (q : ℕ) : Prop :=
  ∀ i : Bool, ∃ (U : Space (Vec (SelIdx p.b p.j))) (V : Space (Vec (AIdx p.g n))),
    (∀ z, sPin a z i ≤ tensorCross U V) ∧
    (∀ z x, x ∈ sPin a z i → Matrix.rank (flattenMatrix.symm x) ≤ q →
      x ∈ tensorRectangle U V) ∧
    LinearIndependent F (U.mkQ ∘ (fun j : CallsAt v i => selV p.j (v.sel j.val))) ∧
    LinearIndependent F (V.mkQ ∘ (fun j : CallsAt v i => baseV (v.par j.val)))

theorem affine_pin_extractors [DecidableEq I] (v : Volley p n I) (a : Plan p n) (q : ℕ)
    (hv : affineAvoids v a q) (i : Bool) :
    ∃ E : Ray p n →ₗ[F] Vec (CallsAt v i),
      (∀ j : CallsAt v i, E (v.rayAt j.val)=Pi.single j 1) ∧
      ∀ z, sPin a z i ≤ E.ker := by
  classical
  obtain ⟨U,V,hpin,_,hs,ht⟩ := hv i
  obtain ⟨E,hE,hL⟩ := selected_tensor_extractors U V _ _ hs ht
  exact ⟨E,hE,fun z => (hpin z).trans hL⟩

theorem affine_key_miss (v : Volley p n I) (t : Tagging p I) (a : Plan p n) (q : ℕ)
    (hv : affineAvoids v a q) (z : Place p) (c : Vec (Volley.visits p t z.1))
    (hc : v.keyM t z.1 *ᵥ c ∈ tabSpace a z) : c=0 := by
  classical
  funext j
  let i := v.obj j.val
  obtain ⟨E,hE,hpin⟩ := affine_pin_extractors v a q hv i
  have hproj := (tab_mem a z _).mp hc i
  rw [v.key_proj] at hproj
  have hz : E (∑ k ∈ v.visitH t i z.1, c k • v.rayAt k.val)=0 := hpin z hproj
  let jj : CallsAt v i := ⟨j.val,by simp [Volley.here,i]⟩
  have hj : j ∈ v.visitH t i z.1 := by simp [Volley.visitH,i]
  have he : (E (∑ k ∈ v.visitH t i z.1, c k • v.rayAt k.val)) jj=c j := by
    rw [map_sum,Finset.sum_apply,Finset.sum_eq_single j]
    · rw [map_smul,hE jj]
      simp [jj]
    · intro k hk' hk
      have hkhere : k.val ∈ v.here i := (v.visitH_here ..).mp hk'
      let kk : CallsAt v i := ⟨k.val,hkhere⟩
      rw [map_smul,hE kk]
      have hne : jj ≠ kk := fun h => hk (Subtype.ext (congrArg Subtype.val h).symm)
      simp [Pi.single_eq_of_ne hne]
    · intro h
      exact (h hj).elim
  have h := congrFun hz jj
  rw [he] at h
  exact h

theorem affine_key_independent (v : Volley p n I) (t : Tagging p I)
    (a : Plan p n) (q : ℕ) (hv : affineAvoids v a q) (z : Place p) :
    Function.Injective (v.keyM t z.1).mulVec ∧ Disjoint (v.keyPlan t z) (tabSpace a z) := by
  constructor
  · rw [←Matrix.coe_mulVecLin,←LinearMap.ker_eq_bot,Matrix.ker_mulVecLin_eq_bot_iff]
    intro c hc
    apply affine_key_miss v t a q hv z c
    rw [hc]
    exact Submodule.zero_mem _
  · rw [disjoint_iff_inf_le]
    rintro x ⟨⟨c,rfl⟩,hc⟩
    have h := affine_key_miss v t a q hv z c hc
    rw [h,map_zero]
    exact Submodule.zero_mem _

end
end Lax793645Proofs.Simplifications
