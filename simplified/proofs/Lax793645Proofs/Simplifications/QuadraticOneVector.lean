import Lax793645Proofs.Simplifications.RelativeQuadraticKernel
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type} [AddCommGroup V] [Module QField V]

private lemma quadratic_plane_value (q : QuadraticForm QField V) (a u v : V)
    (huv : q.polarBilin u v ≠ 0) (e : QField) :
    q a=e ∨ q (a+u)=e ∨ q (a+v)=e ∨ q (a+u+v)=e := by
  by_contra h
  push Not at h
  have same (x y : QField) (hx : x≠e) (hy : y≠e) : x=y := by
    have bits : ∀ z : QField,z=0∨z=1 := by decide
    rcases bits e with he|he <;> rcases bits x with hx'|hx' <;>
      rcases bits y with hy'|hy' <;> simp_all
  have h₁ := same _ _ h.2.1 h.1
  have h₂ := same _ _ h.2.2.1 h.1
  have h₃ := same _ _ h.2.2.2 h.1
  have h₄ := QuadraticMap.map_add q (a+u) v
  have h₅ := QuadraticMap.map_add q a v
  rw [←QuadraticMap.polarBilin_apply_apply] at h₄ h₅
  simp only [map_add,LinearMap.add_apply] at h₄
  rw [h₁,h₃] at h₄
  rw [h₂] at h₅
  apply huv
  linear_combination h₅-h₄

/-- One-vector quadratic extension, using an affine plane rather than a
quadratic character sum. -/
theorem quadratic_one_vector [FiniteDimensional QField V]
    (q : QuadraticForm QField V) (hnd : q.polarBilin.Nondegenerate)
    (D : Submodule QField V) (b : D→ₗ[QField] QField) (e : QField)
    (hroom : 2*Module.finrank QField D+4≤Module.finrank QField V) :
    ∃ v : V,v∉D ∧ q v=e ∧ ∀ d : D,q.polarBilin d v=b d := by
  classical
  let β : LinearMap.BilinForm QField V := q.polarBilin
  let T := β.orthogonal D
  have hd : Module.finrank QField D+Module.finrank QField T=Module.finrank QField V := by
    have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (K:=QField) (V:=V) (B:=β) D
    have hk : LinearMap.ker β=⊥ := LinearMap.BilinForm.Nondegenerate.ker_eq_bot hnd
    change Module.finrank QField D+Module.finrank QField T=
      Module.finrank QField V+Module.finrank QField (D⊓LinearMap.ker β : Submodule QField V) at h
    rw [hk,inf_bot_eq,finrank_bot,add_zero] at h
    exact h
  obtain ⟨b',hb'⟩ := LinearMap.dualMap_surjective_of_injective D.injective_subtype b
  let a := (β.toDual hnd).symm b'
  have ha (d : D) : q.polarBilin d a=b d := by
    calc
      q.polarBilin d a=q.polarBilin a d := by
        simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_comm]
      _=b' d := LinearMap.BilinForm.apply_toDual_symm_apply (B:=β) (hB:=hnd) b' d
      _=b d := LinearMap.congr_fun hb' d
  have huv : ∃ u∈T,∃ v∈T,q.polarBilin u v≠0 := by
    by_contra h
    push Not at h
    have hle : T≤β.orthogonal T := by
      intro v hv u hu
      exact h u hu v hv
    have hm := Submodule.finrank_mono hle
    have ho := LinearMap.BilinForm.finrank_orthogonal (B:=β) hnd T
    omega
  obtain ⟨u,hu,v,hv,huv⟩ := huv
  let U := Submodule.span QField ({u,v}:Set V)
  have huU : u∈U := Submodule.subset_span (by simp)
  have hvU : v∈U := Submodule.subset_span (by simp)
  have hUT : U≤T := Submodule.span_le.mpr (by
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl <;> assumption)
  have hUdim : Module.finrank QField U≤2 := by
    have h := finrank_span_finset_le_card (R:=QField) ({u,v}:Finset V)
    have hc : ({u,v}:Finset V).card≤2 := by
      by_cases h : u=v <;> simp [h]
    have hs : (({u,v}:Finset V):Set V)={u,v} := by ext x; simp
    change Module.finrank QField (Submodule.span QField (({u,v}:Finset V):Set V))≤_ at h
    rw [hs] at h
    exact h.trans hc
  have hDU : Module.finrank QField (D⊔U : Submodule QField V)≤Module.finrank QField D+2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq D U
    omega
  obtain ⟨z,hzT,hz⟩ : ∃ z∈T,a+z∉D⊔U := by
    by_cases haDU : a∈D⊔U
    · have hn : ¬T≤D⊔U := by
        intro hle
        have hm := Submodule.finrank_mono hle
        omega
      change ¬∀ x,x∈T→x∈D⊔U at hn
      push Not at hn
      obtain ⟨z,hz,hzout⟩ := hn
      refine ⟨z,hz,?_⟩
      intro haz
      exact hzout (((D⊔U).add_mem_iff_right haDU).mp haz)
    · exact ⟨0,T.zero_mem,by simpa using haDU⟩
  have hplane (w : V) (hw : w∈U) : a+z+w∉D := by
    intro hd'
    have h₁ : a+z+w∈D⊔U := (show D≤D⊔U from le_sup_left) hd'
    have h₂ : w∈D⊔U := (show U≤D⊔U from le_sup_right) hw
    exact hz (((D⊔U).add_mem_iff_left h₂).mp h₁)
  have hpairs (w : V) (hw : w∈U) (d : D) : q.polarBilin d (a+z+w)=b d := by
    have hz0 : q.polarBilin d z=0 := hzT d d.property
    have hw0 : q.polarBilin d w=0 := hUT hw d d.property
    simp only [map_add,ha,hz0,hw0,add_zero]
  rcases quadratic_plane_value q (a+z) u v huv e with he|he|he|he
  · exact ⟨a+z,by simpa using hplane 0 U.zero_mem,he,
      by intro d; simpa using hpairs 0 U.zero_mem d⟩
  · exact ⟨a+z+u,hplane u huU,he,hpairs u huU⟩
  · exact ⟨a+z+v,hplane v hvU,he,hpairs v hvU⟩
  · refine ⟨a+z+(u+v),hplane (u+v) (U.add_mem huU hvU),?_,
      hpairs (u+v) (U.add_mem huU hvU)⟩
    simpa only [add_assoc] using he

end
end Lax793645Proofs.Simplifications
