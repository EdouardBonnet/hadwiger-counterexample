import Lax793645Proofs.Simplifications.QuadraticEmbedding
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

namespace Lax793645Proofs.Simplifications
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type} [AddCommGroup V] [Module QField V]

theorem binary_polar_self (q : QuadraticForm QField V) (v : V) :
    q.polarBilin v v=0 := by
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self]
  simpa only [two_smul] using (ZModModule.add_self (q v))

theorem binary_polar_symm (q : QuadraticForm QField V) (v w : V) :
    q.polarBilin v w=q.polarBilin w v := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_comm]

def quadraticTransvectionLinear (q : QuadraticForm QField V) (v : V) : V→ₗ[QField] V :=
  LinearMap.id+(q.polarBilin v).smulRight v

theorem quadratic_transvection_apply (q : QuadraticForm QField V) (v x : V) :
    quadraticTransvectionLinear q v x=x+q.polarBilin v x • v := rfl

theorem quadratic_transvection_involutive (q : QuadraticForm QField V) (v : V) :
    Function.Involutive (quadraticTransvectionLinear q v) := by
  intro x
  have hb : q.polarBilin v (quadraticTransvectionLinear q v x)=q.polarBilin v x := by
    rw [quadratic_transvection_apply,map_add,map_smul,binary_polar_self,smul_zero,add_zero]
  rw [quadratic_transvection_apply,hb,quadratic_transvection_apply,add_assoc,
    ZModModule.add_self,add_zero]

theorem quadratic_transvection_preserves (q : QuadraticForm QField V) (v : V)
    (hv : q v=1) (x : V) : q (quadraticTransvectionLinear q v x)=q x := by
  rcases (by decide : ∀ a : QField,a=0∨a=1) (q.polarBilin v x) with hx|hx
  · simp [quadratic_transvection_apply,hx]
  rw [quadratic_transvection_apply,hx,one_smul,QuadraticMap.map_add q,
    ←QuadraticMap.polarBilin_apply_apply,binary_polar_symm q x v,hx,hv]
  rw [add_assoc,ZModModule.add_self,add_zero]

/-- A quadratic reflection in a vector of quadratic value one. -/
def quadraticTransvection (q : QuadraticForm QField V) (v : V) (hv : q v=1) :
    q.IsometryEquiv q where
  toLinearMap:=quadraticTransvectionLinear q v
  invFun:=quadraticTransvectionLinear q v
  left_inv:=quadratic_transvection_involutive q v
  right_inv:=quadratic_transvection_involutive q v
  map_app':=quadratic_transvection_preserves q v hv

theorem quadratic_transvection_fix (q : QuadraticForm QField V) (v : V) (hv : q v=1)
    (x : V) (hx : q.polarBilin v x=0) : quadraticTransvection q v hv x=x := by
  change quadraticTransvectionLinear q v x=x
  rw [quadratic_transvection_apply,hx,zero_smul,add_zero]

/-- Equal quadratic values and polar pairing one are enough for a single
reflection to interchange two vectors, while fixing their common polar data. -/
theorem quadratic_move_pair (q : QuadraticForm QField V) (u w : V)
    (hq : q u=q w) (huw : q.polarBilin u w=1) :
    ∃ e : q.IsometryEquiv q,e u=w ∧
      ∀ x,q.polarBilin u x=q.polarBilin w x → e x=x := by
  have hv : q (u+w)=1 := by
    rw [QuadraticMap.map_add q,←QuadraticMap.polarBilin_apply_apply,hq,huw,
      ZModModule.add_self,zero_add]
  refine ⟨quadraticTransvection q (u+w) hv,?_,?_⟩
  · change quadraticTransvectionLinear q (u+w) u=w
    rw [quadratic_transvection_apply,map_add,LinearMap.add_apply,binary_polar_self,
      zero_add,binary_polar_symm q w u,huw,one_smul]
    rw [←add_assoc,ZModModule.add_self,zero_add]
  · intro x hx
    apply quadratic_transvection_fix
    rw [map_add,LinearMap.add_apply,hx,ZModModule.add_self]

theorem binary_span_decompose (D : Submodule QField V) (u x : V)
    (hx : x∈D⊔Submodule.span QField {u}) :
    ∃ d : D,x=(d:V) ∨ x=(d:V)+u := by
  obtain ⟨d,hd,v,hv,he⟩:=Submodule.mem_sup.mp hx
  obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
  rcases (by decide : ∀ a : QField,a=0∨a=1) a with rfl|rfl
  · exact ⟨⟨d,hd⟩,Or.inl (by simpa using he.symm)⟩
  · exact ⟨⟨d,hd⟩,Or.inr (by simpa using he.symm)⟩

end
end Lax793645Proofs.Simplifications
