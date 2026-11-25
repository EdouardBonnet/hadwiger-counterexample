import Lax793645Proofs.Simplifications.OneFreeChannelLaws

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {p : Shape} {n N : ℕ}

theorem one_unit_component_cap {w : Wgt (OneUnit p n N)} {H : ℝ}
    (m : Mixer p n) (i : Bool)
    (hcap : ∀ o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N) (e : Comp p.g) (P : OneFrame p n N) :
    mapW w (fun x=>x i e) P≤H*
      quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
        (selfM p n m.mixM).toQuadraticForm' P := by
  have hh:=mapW_cap hcap (fun o=>o e) P
  rw [mapW_nested] at hh
  have hc:=product_projection_law
    (fun _ : Comp p.g=>quadraticChannelRaw (C:=Vec (Fin p.h))
      (hyperbolicMatrix N).toQuadraticForm' (selfM p n m.mixM).toQuadraticForm')
    (fun _=>unifOn_law (quadratic_channel_frames_exist
      (hyperbolicMatrix N).toQuadraticForm' (hyperbolic_matrix_nondegenerate N)
      (selfM p n m.mixM).toQuadraticForm' (C:=Vec (Fin p.h)) (one_frame_room hroom))) e
  have hc' : mapW (oneRaw m N) (fun o=>o e)=
      quadraticChannelRaw (C:=Vec (Fin p.h)) (hyperbolicMatrix N).toQuadraticForm'
        (selfM p n m.mixM).toQuadraticForm' := by
    convert hc using 1 <;> congr!
  rw [hc'] at hh
  exact hh

theorem one_unit_glimpse_failure {w : Wgt (OneUnit p n N)} {H : ℝ}
    (m : Mixer p n) (hH : 0≤H) (i : Bool)
    (hcap : ∀ o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (e : Comp p.g) {d : ℕ} (T : Mat (Fin (2*N)) (Fin d))
    (hT : Function.Injective T.mulVec) :
    pr w (fun x=>¬Function.Injective ((onePhaseCube (x i) e).1ᵀ*T).mulVec)≤
      H*2*bp ((d:ℝ)-p.h) := by
  let E (P : OneFrame p n N):=
    ¬Function.Injective (((oneChannelPairEquiv p N (oneChannels P)).1)ᵀ*T).mulVec
  have hh:=pr_cap (one_unit_component_cap m i hcap hroom e) E
  rw [mapW_pr] at hh
  apply hh.trans
  exact (mul_le_mul_of_nonneg_left
    (one_free_channel_glimpse m (hroom.trans (by omega)) T hT) hH).trans_eq (by ring)

abbrev OneCover (p : Shape) (N : ℕ) := Comp p.g→Space (Vec (Fin (2*N)))

def oneCoverDimension (C : OneCover p N) : ℕ:=∑ e,dim (C e)

def oneCoverGlimpse (x : OneUnit p n N) (C : OneCover p N) : Prop :=
  ∀ i e,Function.Injective ((onePhaseCube (x i) e).1ᵀ*pack (C e)).mulVec

/-- The simultaneous cover test uses only the free channel block. The
cost is linear in the number of components and has no Gram price. -/
theorem one_cover_glimpse_failure {w : Wgt (OneUnit p n N)} {H : ℝ}
    (m : Mixer p n) (hw : SubLaw w) (hH : 0≤H)
    (hcap : ∀ i o,mapW w (fun x=>x i) o≤H*oneRaw m N o)
    (hroom : Fintype.card (Row p n)+2*p.h+1≤N)
    (C : OneCover p N) (d : ℕ) (hd : oneCoverDimension C≤d) :
    pr w (fun x=>¬oneCoverGlimpse x C)≤
      4*num (Comp p.g)*H*bp ((d:ℝ)-p.h) := by
  classical
  let P (z : Bool×Comp p.g) (x : OneUnit p n N):=
    ¬Function.Injective ((onePhaseCube (x z.1) z.2).1ᵀ*pack (C z.2)).mulVec
  have he x : ¬oneCoverGlimpse x C→∃ z,P z x := by
    simp only [oneCoverGlimpse,not_forall]
    rintro ⟨i,e,h⟩
    exact ⟨(i,e),h⟩
  apply ((pr_mono hw.nz he).trans (pr_exists_le hw.nz P)).trans
  have hb (z : Bool×Comp p.g) : pr w (P z)≤H*2*bp ((d:ℝ)-p.h) := by
    apply (one_unit_glimpse_failure m hH z.1 (hcap z.1) hroom z.2 _ (pack_inj _)).trans
    apply mul_le_mul_of_nonneg_left (bp_le ?_) (by positivity)
    have hdim : dim (C z.2)≤d:=
      (Finset.single_le_sum (fun e _=>Nat.zero_le (dim (C e))) (Finset.mem_univ z.2)).trans hd
    exact sub_le_sub_right (by exact_mod_cast hdim) _
  apply (Finset.sum_le_sum (fun z _=>hb z)).trans_eq
  simp [num,Finset.sum_const,Fintype.card_prod]
  ring

end
end Lax793645Proofs.Simplifications
