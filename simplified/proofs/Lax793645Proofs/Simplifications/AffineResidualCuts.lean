import Lax793645Proofs.Simplifications.AffineKeyDirections
import Lax793645Proofs.Simplifications.TensorMatrixRead
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ResidualCutPairs

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule Module LinearMap Finset
open scoped BigOperators
noncomputable section

variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

/-- Common protected spaces and their selected-point extractors. This is
the entire interface used after subtracting the selected atoms. -/
structure RaySeparation (v : Volley p n I) (a : Plan p n) where
  space : Bool → Space (Ray p n)
  read : (i : Bool) → Ray p n →ₗ[F] Vec (CallsAt v i)
  onKeys : ∀ i (j : CallsAt v i), read i (v.rayAt j.val)=Pi.single j 1
  vanishes : ∀ i, space i ≤ (read i).ker
  pins : ∀ i z, sPin a z i ≤ space i

namespace RaySeparation
variable {v : Volley p n I} {a : Plan p n} (H : RaySeparation v a)

theorem read_projection (t : Tagging p I) (i : Bool) (e : Comp p.g)
    (c : Vec (Volley.visits p t e)) (j : Volley.visits p t e)
    (hj : j.val ∈ v.here i) :
    H.read i ((IP p n i)ᵀ *ᵥ (v.keyM t e *ᵥ c)) ⟨j.val,hj⟩=c j := by
  classical
  rw [v.key_proj,map_sum,Finset.sum_apply,Finset.sum_eq_single j]
  · rw [map_smul,H.onKeys i ⟨j.val,hj⟩]
    simp
  · intro k hk hkj
    let kk : CallsAt v i := ⟨k.val,(v.visitH_here ..).mp hk⟩
    rw [map_smul,H.onKeys i kk]
    have hne : (⟨j.val,hj⟩ : CallsAt v i) ≠ kk := fun h =>
      hkj (Subtype.ext (congrArg Subtype.val h).symm)
    simp [Pi.single_eq_of_ne hne]
  · intro h
    exact (h ((v.visitH_here ..).mpr hj)).elim

theorem projection_coefficients (t : Tagging p I) (x : Ray p n) (z : Place p)
    (i : Bool) (hx : x ∈ H.space i) (c : Vec (Volley.visits p t z.1))
    (hc : x-(IP p n i)ᵀ *ᵥ (v.keyM t z.1 *ᵥ c) ∈ sPin a z i) :
    ∀ j ∈ v.visitH t i z.1, c j=0 := by
  have he : H.read i (x-(IP p n i)ᵀ *ᵥ (v.keyM t z.1 *ᵥ c))=0 :=
    H.vanishes i (H.pins i z hc)
  rw [map_sub,show H.read i x=0 from H.vanishes i hx,zero_sub,neg_eq_zero] at he
  intro j hj
  have h := congrFun he (⟨j.val,(v.visitH_here ..).mp hj⟩ : CallsAt v i)
  rwa [H.read_projection t i z.1 c j ((v.visitH_here ..).mp hj)] at h

theorem read_off_star (t : Tagging p I) (i : Bool) (j : CallsAt v i) (z : Place p)
    (hj : ¬inc z.1 (t j.val)) (x : Ray p n) (hx : x ∈ sPin (v.frozen a t) z i) :
    H.read i x j=0 := by
  classical
  rw [v.sPin_frozen,Submodule.mem_sup] at hx
  obtain ⟨y,hy,k,⟨k,⟨c,rfl⟩,rfl⟩,rfl⟩ := hx
  have he : H.read i y=0 := H.vanishes i (H.pins i z hy)
  rw [map_add,Pi.add_apply,he,Pi.zero_apply,zero_add]
  change H.read i ((IP p n i)ᵀ *ᵥ (v.keyM t z.1 *ᵥ c)) j=0
  rw [v.key_proj,map_sum,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro u hu
  let uu : CallsAt v i := ⟨u.val,(v.visitH_here ..).mp hu⟩
  rw [map_smul,H.onKeys i uu]
  have hne : j ≠ uu := by
    intro h
    have e : j.val=u.val := congrArg Subtype.val h
    apply hj
    rw [e]
    exact u.property
  simp [Pi.single_eq_of_ne hne]

theorem component_read_off_star (t : Tagging p I) {b : Plan p n} {C : ChanOut p n}
    {mode : Bool} {x : Xpair p n} (ho : orth p C (v.frozen a t) b mode x)
    (i : Bool) (j : CallsAt v i) (e : Comp p.g) (hj : ¬inc e (t j.val)) :
    matrixRead (H.read i) j ((x i).val e)=0 := by
  classical
  let E := LinearMap.toMatrix' (H.read i)
  have hφ (c : Bool) : E.row j ∈ annih (sPin (v.frozen a t) (e,c) i) := by
    apply coordinate_test_annih
    intro u hu
    change (E*ᵥ u) j=0
    have he : E*ᵥ u=H.read i u := LinearMap.congr_fun (toMat_map _) u
    rw [he]
    exact H.read_off_star t i j (e,c) hj u hu
  rw [matrixRead_eval]
  exact vanish_one ho i e _ (hφ true) _ (hφ false)

theorem unfreeze_projection (t : Tagging p I) (x : Ray p n) (z : Place p) (i : Bool)
    (hx : x ∈ H.space i) (hf : x ∈ sPin (v.frozen a t) z i) : x ∈ sPin a z i := by
  classical
  rw [v.sPin_frozen,Submodule.mem_sup] at hf
  obtain ⟨y,hy,k,⟨k,⟨c,rfl⟩,rfl⟩,he⟩ := hf
  have hd : x-(IP p n i)ᵀ *ᵥ (v.keyM t z.1 *ᵥ c)=y := by
    rw [←he]; exact add_sub_cancel_right _ _
  have hz := H.projection_coefficients t x z i hx c (hd ▸ hy)
  rw [v.key_proj,Finset.sum_eq_zero (fun j hj => by rw [hz j hj,zero_smul]),sub_zero] at hd
  rwa [hd]

theorem unfreeze_pin (t : Tagging p I) (x : Ray p n) (z : Place p) (i : Bool)
    (hx : x ∈ H.space i) (hf : IP p n i *ᵥ x ∈ v.frozen a t z) :
    IP p n i *ᵥ x ∈ a z := by
  classical
  obtain ⟨d,hd,k,⟨c,rfl⟩,he⟩ := Submodule.mem_sup.mp hf
  have hc : c=0 := by
    funext j
    let k := v.obj j.val
    let y := (IP p n k)ᵀ *ᵥ (IP p n i *ᵥ x)
    have hy : y-(IP p n k)ᵀ *ᵥ (v.keyM t z.1 *ᵥ c) ∈ sPin a z k := by
      unfold y
      rw [←he,Matrix.mulVec_add]
      change (IP p n k)ᵀ *ᵥ d+_-(IP p n k)ᵀ *ᵥ (_ *ᵥ _) ∈ _
      rw [mulVecLin_apply,add_sub_cancel_right]
      exact ⟨d,hd,rfl⟩
    have hY : y ∈ H.space k := by
      unfold y
      rw [Matrix.mulVec_mulVec]
      by_cases hk : k=i
      · rw [hk,IP_self,Matrix.one_mulVec]
        exact hx
      rw [IP_cross hk,Matrix.zero_mulVec]
      exact Submodule.zero_mem _
    exact H.projection_coefficients t y z k hY c hy j (by simp [Volley.visitH,k])
  rw [hc,map_zero,add_zero] at he
  rwa [←he]

/-- The residual becomes effective using containment in the protected spaces.
The proof neither bounds its rank nor reconstructs its selector labels. -/
theorem residual_effective (t : Tagging p I) {b : Plan p n} {j : Bool}
    (M : Cross p n) (x : Xpair p n)
    (ho : orth p (channelOut p M j) (v.frozen a t) b j x)
    (hi : tableInj a b M) (i : Bool)
    (hx : ∀ e, colSp ((x i).val e) ≤ H.space i) :
    (x i).val ∈ effective a i := by
  classical
  refine effective_mem.mpr ⟨(x i).property,fun e => ?_⟩
  let A := (x i).val e
  let P (c) := sPin (v.frozen a t) (e,c) i
  have hd (c : Bool) (φ : Ray p n) (hφ : φ ∈ annih (P (!c))) : A*ᵥ φ=0 := by
    have hA : A*ᵥ φ ∈ H.space i := hx e ⟨φ,rfl⟩
    have hp := orth_ip_frozen ho i (e,c) φ hφ
    exact hi (e,c) i j (A*ᵥ φ) (H.unfreeze_pin t _ _ i hA hp)
      (orth_delta_probe ho i (e,c) φ hφ)
  have hsym : Aᵀ=A := orth_pair_sym x e i
  have hp (c : Bool) : colSp A ≤ sPin a (e,c) i := by
    have hf : colSp A ≤ P c := by
      have h : colSp A ≤ annih (annih (P c)) := (colSp_kill ..).mpr (fun φ hφ => by
        rw [hsym]
        exact hd (!c) φ (by simpa using hφ))
      rwa [annih_annih] at h
    rintro y ⟨u,rfl⟩
    exact H.unfreeze_projection t _ _ i (hx e ⟨u,rfl⟩) (hf ⟨u,rfl⟩)
  change A ∈ box _ _
  rw [box_mem,hsym]
  exact ⟨hp _,hp _⟩

end RaySeparation
end
end Lax793645Proofs.Simplifications
