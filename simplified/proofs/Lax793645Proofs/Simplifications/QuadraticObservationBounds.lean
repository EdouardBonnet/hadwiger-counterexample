import Lax793645Proofs.Simplifications.QuadraticFrameLowerBound
import Lax793645Proofs.Simplifications.QuadraticMomentMaps

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem constant_orbit_cap {A : Type} [Fintype A] {w : Wgt A} (hw : SubLaw w)
    (p : A→Prop) (x : A) (hx : p x) (he : ∀ y,p y→w y=w x) :
    w x≤unifOn p x := by
  have hn : 0<nbr p := by
    have hh : (1:ℝ)≤nbr p := by
      calc
        1=ind (p x):=(ind_one hx).symm
        _ ≤ nbr p:=Finset.single_le_sum (fun i _=>ind_nonneg (p i)) (Finset.mem_univ x)
    linarith
  have hmass : w x*nbr p=pr w p := by
    unfold nbr tot pr avg
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : p y
    · rw [he y hy]
    · simp only [ind_zero hy,mul_zero]
  rw [unifOn_val,ind_one hx,le_div_iff₀ hn]
  rw [hmass]
  exact (pr_le_tot hw.nz).trans hw.total

variable {B V R : Type} [AddCommGroup B] [Module QField B]
  [AddCommGroup V] [Module QField V] [AddCommGroup R] [Module QField R]
  [FiniteDimensional QField B] [FiniteDimensional QField V] [FiniteDimensional QField R]
  [Fintype (B→ₗ[QField]V)] [Fintype (R→ₗ[QField]V)]

omit [FiniteDimensional QField B] in
/-- No prescribed quadratic form on the observed subspace is required here.
For any class of own-frame data, an image atom is bounded by its quadratic
orbit. This is the version needed for arbitrary stored pins. -/
theorem quadratic_frames_observation_cap
    (q : QuadraticForm QField V) (hnd : q.polarBilin.Nondegenerate)
    (C : QuadraticForm QField B→Prop)
    (hc : ∃ P,quadraticFramesAt q C P)
    (J : R→ₗ[QField]B) (hJ : Function.Injective J)
    (hroom : 2*Module.finrank QField R+6≤Module.finrank QField V)
    (T : R→ₗ[QField]V) :
    mapW (unifOn (quadraticFramesAt q C)) (fun P=>P.comp J) T≤
      unifOn (quadraticGramGood q (q.comp T)) T := by
  let w:=mapW (unifOn (quadraticFramesAt q C)) (fun P=>P.comp J)
  have hw : IsLaw w:=mapW_law (unifOn_law hc) _
  by_cases hT : Function.Injective T
  · apply constant_orbit_cap hw.sub _ T ⟨hT,rfl⟩
    intro Y hY
    have hval (r : R) : q (Y r)=q (T r):=
      congrArg (fun Q : QuadraticForm QField R=>Q r) hY.2
    obtain ⟨e,he⟩:=quadratic_frame_symmetry q hnd Y T hY.1 hT hval
    have hf (P : B→ₗ[QField]V) : P.comp J=Y↔(quadraticPost q e P).comp J=T := by
      constructor
      · intro h
        apply LinearMap.ext
        intro r
        change e (P (J r))=T r
        have hr : P (J r)=Y r:=LinearMap.congr_fun h r
        rw [hr]
        exact he r
      · intro h
        apply LinearMap.ext
        intro r
        apply e.injective
        exact (LinearMap.congr_fun h r).trans (he r).symm
    change pr (unifOn (quadraticFramesAt q C)) (fun P=>P.comp J=Y)=
      pr (unifOn (quadraticFramesAt q C)) (fun P=>P.comp J=T)
    unfold pr
    rw [←avg_bij (quadraticPost q e) (unifOn (quadraticFramesAt q C))
      (fun P=>ind (P.comp J=T))]
    simp_rw [unifOn_val,←quadratic_post_invar q e C,←hf]
    rfl
  · have hz : carried w (fun Y=>Function.Injective Y) :=
      mapW_carried (unifOn_carried _) (fun P hP=>hP.1.comp hJ)
    change w T≤_
    rw [hz T hT]
    exact (unifOn_sub _).nz _

end
end Lax793645Proofs.Simplifications
