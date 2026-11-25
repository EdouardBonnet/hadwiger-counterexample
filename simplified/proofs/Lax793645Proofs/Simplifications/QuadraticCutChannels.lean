import Lax793645Proofs.Simplifications.QuadraticCutSolvability

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Submodule
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n : ℕ}

def frozenChannelKernel {I : Type} [Fintype I] (h : ℕ) (P : Space (Vec I))
    (C : Space (Hyperbolic h)) (g₀ : P→ₗ[F]Hyperbolic h) : Space (Vec I) :=
  (C.comap g₀).map P.subtype

theorem frozen_channel_kernel_le {I : Type} [Fintype I] (h : ℕ) (P : Space (Vec I))
    (C : Space (Hyperbolic h)) (g₀ : P→ₗ[F]Hyperbolic h) :
    frozenChannelKernel h P C g₀≤P := by
  rintro v ⟨f,_,rfl⟩
  exact f.property

theorem frozen_channel_kernel_mem {I : Type} [Fintype I] (h : ℕ) (P : Space (Vec I))
    (C : Space (Hyperbolic h)) (g₀ : P→ₗ[F]Hyperbolic h) (f : P) (hf : g₀ f∈C) :
    f.val∈frozenChannelKernel h P C g₀ := ⟨f,hf,rfl⟩

/-- Complete the bounded-rank quadratic target and realize it by genuine
hyperbolic channel maps. This is for one cut-profile space; it does not
assume independence or nonvanishing of the frozen channel images. -/
theorem quadratic_cut_channels
    (h : ℕ) (P : Comp p.g→Space (Ray p n)) (C : Comp p.g→Space (Hyperbolic h))
    (g₀ : ∀ e,P e→ₗ[F]Hyperbolic h) (ell : ∀ e,Ray p n→ₗ[F]C e→ₗ[F]F)
    (M B : Profile p n) (f c b r : ℕ)
    (hP : ∀ e,dim (P e)≤f) (hC : ∀ e,dim (C e)≤c)
    (hM : ∀ e,(M e).rank≤r) (hB : ∀ e,(B e).rank≤b)
    (hval : ∀ e,∀ v : P e,(B e).toQuadraticForm' v=hyperbolicQuadratic h (g₀ e v))
    (hcompat : ∀ e,∀ (v : P e) (a : C e),
      ell e v a=(hyperbolicQuadratic h).polarBilin (g₀ e v) a)
    (hrow : ∀ e,∀ (v : P e) (hv : g₀ e v∈C e) (w : Ray p n),
      (B e).toQuadraticForm'.polarBilin v w=ell e w ⟨g₀ e v,hv⟩)
    (hobs : ∀ x∈Xspace p n,
      x∈quadraticCutConstraints P (fun e=>frozenChannelKernel h (P e) (C e) (g₀ e))→
        cutMatrixFunctional M x=cutMatrixFunctional B x)
    (hroom : 2*(r+b+drow p f (2*f+b))+3*c+f+2≤h) :
    ∃ (Q : Profile p n) (g : Comp p.g→Ray p n→ₗ[F]Hyperbolic h),
      (∀ e,∀ v,hyperbolicQuadratic h (g e v)=(Q e).toQuadraticForm' v) ∧
      (∀ e,∀ v : P e,g e v=g₀ e v) ∧
      (∀ e,∀ (v : Ray p n) (a : C e),(hyperbolicQuadratic h).polarBilin (g e v) a=ell e v a) ∧
      (∀ x∈Xspace p n,cutMatrixFunctional Q x=cutMatrixFunctional M x) ∧
      ∀ e,(Q e).rank≤r+b+drow p f (2*f+b) := by
  classical
  let K (e : Comp p.g):=frozenChannelKernel h (P e) (C e) (g₀ e)
  have hK (e : Comp p.g) : K e≤P e:=frozen_channel_kernel_le h (P e) (C e) (g₀ e)
  let G:=(cutMatrixFunctional (M+B)).comp (Xspace p n).subtype
  have hG (x : Xspace p n) (hx : x.val∈quadraticCutConstraints P K) : G x=0 := by
    change cutMatrixFunctional (M+B) x.val=0
    rw [cut_matrix_functional_add,hobs x.val x.property hx,char_two]
  obtain ⟨Z,hZ,hZv,hZr⟩:=quadratic_cut_target_solvable P K G hG
  have hQval (e : Comp p.g) (v : Ray p n) (hv : v∈P e) :
      ((Z+B) e).toQuadraticForm' v=(B e).toQuadraticForm' v := by
    simp only [Pi.add_apply,matrix_quadratic_add,hZv e v hv,zero_add]
  have hQrow (e : Comp p.g) (k : Ray p n) (hk : k∈K e) (v : Ray p n) :
      ((Z+B) e).toQuadraticForm'.polarBilin k v=(B e).toQuadraticForm'.polarBilin k v := by
    simp only [Pi.add_apply,matrix_polar_add,hZr e k hk v,zero_add]
  have hQobs (x : Profile p n) (hx : x∈Xspace p n) :
      cutMatrixFunctional (Z+B) x=cutMatrixFunctional M x := by
    have hz:=hZ ⟨x,hx⟩
    change cutMatrixFunctional Z x=cutMatrixFunctional (M+B) x at hz
    rw [cut_matrix_functional_add,hz,cut_matrix_functional_add,add_assoc,char_two,add_zero]
  obtain ⟨Q,hQv,hQr,hQo,hQrank⟩:=quadratic_bounded_cut_target P K M B (Z+B)
    f b r hP hK hM hB hQval hQrow hQobs
  have hreal (e : Comp p.g) := quadratic_matrix_realize h (Q e) (P e) (C e) (g₀ e) (ell e)
    (fun v=>(hQv e v v.property).trans (hval e v)) (hcompat e)
    (fun v hv w=>(hQr e v (frozen_channel_kernel_mem h (P e) (C e) (g₀ e) v hv) w).trans
      (hrow e v hv w))
    (show 2*(Q e).rank+3*dim (C e)+dim (P e)+2≤h from
      (Nat.add_le_add_right (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left 2 (hQrank e))
          (Nat.mul_le_mul_left 3 (hC e))) (hP e)) 2).trans hroom)
  choose g hg hv hp using hreal
  exact ⟨Q,g,hg,hv,hp,hQo,hQrank⟩

end
end Lax793645Proofs.Simplifications
