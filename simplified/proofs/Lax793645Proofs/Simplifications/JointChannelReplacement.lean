import Lax793645Proofs.Simplifications.JointQuadraticChannels

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

/-- Replace the actual channel map by a realization of the target. The
small baseline is constructed here; its rank is only f+c. No rank bound
on the original channel map or its quadratic representative is assumed. -/
theorem joint_channel_replacement
    (h : ℕ) (P : Comp p.g→Space (JointRay p n)) (C : Comp p.g→Space (Hyperbolic h))
    (G : Comp p.g→JointRay p n→ₗ[F]Hyperbolic h) (M A : JointProfile p n)
    (hA : ∀ e v,(A e).toQuadraticForm' v=hyperbolicQuadratic h (G e v))
    (f c r : ℕ) (hP : ∀ e,dim (P e)≤f) (hC : ∀ e,dim (C e)≤c)
    (hM : ∀ e,(M e).rank≤r)
    (hobs : ∀ x∈jointXspace,
      x∈jointQuadraticConstraints P
        (fun e=>frozenChannelKernel h (P e) (C e) ((G e).domRestrict (P e)))→
      jointMatrixFunctional M x=jointMatrixFunctional A x)
    (hroom : r+(f+c)+jointCompressionRank p f (2*f+(f+c))+5*c+6*f+2≤h) :
    ∃ (Q : JointProfile p n) (g : Comp p.g→JointRay p n→ₗ[F]Hyperbolic h),
      (∀ e v,hyperbolicQuadratic h (g e v)=(Q e).toQuadraticForm' v) ∧
      (∀ e,∀ v∈P e,g e v=G e v) ∧
      (∀ e v,∀ a∈C e,(hyperbolicQuadratic h).polarBilin (g e v) a=
        (hyperbolicQuadratic h).polarBilin (G e v) a) ∧
      (∀ x∈jointXspace,jointMatrixFunctional Q x=jointMatrixFunctional M x) ∧
      ∀ e,(Q e).rank≤r+(f+c)+jointCompressionRank p f (2*f+(f+c)) := by
  classical
  let g₀ (e : Comp p.g):=(G e).domRestrict (P e)
  let ell (e : Comp p.g) : JointRay p n→ₗ[F]C e→ₗ[F]F:=
    (hyperbolicQuadratic h).polarBilin.compl₁₂ (G e) (C e).subtype
  have hc (e : Comp p.g) (v : P e) (a : C e) :
      ell e v a=(hyperbolicQuadratic h).polarBilin (g₀ e v) a:=rfl
  choose B hBr hBv hBk using fun e=>quadratic_matrix_baseline h (P e) (C e) (g₀ e) (ell e) (hc e)
  have hb (e : Comp p.g) : (B e).rank≤f+c:=
    (hBr e).trans (Nat.add_le_add (hP e) (hC e))
  let K (e : Comp p.g):=frozenChannelKernel h (P e) (C e) (g₀ e)
  have hr (e : Comp p.g) (k : JointRay p n) (hk : k∈K e) (v : JointRay p n) :
      (B e).toQuadraticForm'.polarBilin k v=(A e).toQuadraticForm'.polarBilin k v := by
    obtain ⟨a,ha,rfl⟩:=hk
    change (B e).toQuadraticForm'.polarBilin a.val v=(A e).toQuadraticForm'.polarBilin a.val v
    rw [hBk e a ha v]
    change (hyperbolicQuadratic h).polarBilin (G e v) (G e a)=_
    rw [binary_polar_symm]
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hA,map_add]
  have hv (e : Comp p.g) (v : JointRay p n) (hv : v∈P e) :
      (B e).toQuadraticForm' v=(A e).toQuadraticForm' v :=
    (hBv e ⟨v,hv⟩).trans (hA e v).symm
  have hh (x : JointProfile p n) (hx : x∈jointXspace) (hquad : x∈jointQuadraticConstraints P K) :
      jointMatrixFunctional M x=jointMatrixFunctional B x := by
    have hz:=((joint_quadratic_annihilator_values P K (B+A)).mpr
      ⟨fun e v hv'=>by simp only [Pi.add_apply,matrix_quadratic_add,hv e v hv',char_two],
       fun e k hk v=>by simp only [Pi.add_apply,matrix_polar_add,hr e k hk v,char_two]⟩) x hquad
    rw [joint_matrix_functional_add,←ZModModule.sub_eq_add,sub_eq_zero] at hz
    exact (hobs x hx hquad).trans hz.symm
  obtain ⟨Q,g,hg,hf,hproj,ho,hqr⟩:=joint_quadratic_channels h P C g₀ ell M B
    f c (f+c) r hP hC hM hb hBv hc hBk hh hroom
  exact ⟨Q,g,hg,(fun e v hv=>hf e ⟨v,hv⟩),
    (fun e v a ha=>hproj e v ⟨a,ha⟩),ho,hqr⟩

end
end Lax793645Proofs.Simplifications
