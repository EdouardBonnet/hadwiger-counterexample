import Lax793645Proofs.Simplifications.CoherentQueryArrays
import Lax793645Proofs.Simplifications.LinearCellPredictors
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SyntheticFailureBounds

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix Function LinearMap Finset Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {p : Shape} {n N d : ℕ}

theorem arches_affine_congr (f g : Vec (Hue d)→F)
    (h : ∀ u,weightsAff u→f u=g u) : arches f=arches g := by
  ext i j
  have hj (i : Hue d) : weightsAff (jet i) := by simp [weightsAff,jet]
  have ht : weightsAff (jet none+jet (incarn i true)+jet (incarn j false)) := by
    simp only [weightsAff,Pi.add_apply,Finset.sum_add_distrib]
    rw [show ∑ k,jet (none : Hue d) k=1 from hj _,
      show ∑ k,jet (incarn i true) k=1 from hj _,
      show ∑ k,jet (incarn j false) k=1 from hj _,char_two,zero_add]
  change f _+f _+(f _+f _)=g _+g _+(g _+g _)
  rw [h _ ht,h _ (hj _),h _ (hj _),h _ (hj _)]

theorem arches_constant_add (a : F) (f : Vec (Hue d)→F) :
    arches (fun u=>a+f u)=arches f := by
  ext i j
  simp only [arches,Matrix.of_apply]
  have ha:=char_two a
  linear_combination 2*ha

theorem beam_rank_le (d : ℕ) : (beamMap d).rank≤d := by
  let f : Sextant d d:=(Function.Embedding.refl _,Function.Embedding.refl _)
  have he : reflectSextant f=Function.Embedding.refl (Hue d) := by
    ext i
    rcases i with _|⟨b,j⟩
    · rfl
    cases b <;> rfl
  have h:=beam_rank f
  rw [cart_target,he] at h
  exact h

/-- At a fixed good frame, the generic prediction forces slope one on
almost every common cell. A finite affine rank test suffices; no comparison
with a synthetic ambient distribution is used. -/
theorem linear_screen_slopes (H : Space (PairedKeys (Comp p.g) (Fin N)))
    [Fintype (Module.Dual F H)] (o : Orient p n N) (s : Label p.b)
    (hfree : Injective ((mixedFrameRowLinear (selectorFreeColumns p n s) o).comp H.subtype))
    (g : Augur p N) (φ : Tag p.g→F→Module.Dual F H→F)
    (hφ : ∀ l q x,g l q (starKey l x)=φ l q (jointCell H x))
    (E : Finset (Tag p.g)) (r : ℕ) (ε : ℝ) (m : Mixer p n)
    (hj : 1≤p.j) (hn : 2*p.r≤n)
    (hroom : 2*r+1≤privateWidth p.g*(p.g-E.card)*p.r)
    (hscreen : screen p o s E r g ε) (l : Tag p.g) :
    pr unif (fun c=>cellSlope (φ l) c=0)≤fiddleRate p (Hue (2*r+1))*ε := by
  classical
  let d:=2*r+1
  let f:=Flavor.full (g:=p.g)
  let C:=Module.Dual F H
  let A0:=(jointCell H).comp (frameFreeKey (selectorFreeColumns p n s) o)
  obtain ⟨S,hS⟩:=A0.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (joint_cell_free_surjective _ o H hfree))
  have hS' (c : C) : A0 (S c)=c:=LinearMap.congr_fun hS c
  obtain ⟨a,ha,hclean⟩:=masked_punch_real p l E (beamMap d)
    ((beam_rank_le d).trans (hroom.trans (coordinate_tester_room p l E)))
  obtain ⟨w,hw,hrep⟩:=hscreen
  obtain ⟨M,hM,hm⟩:=hrep l
  let P:=mismatch p g w l s f o
  let μ:=pairW (sketchLaw p n a) (unif : Wgt C)
  let repair (x : (Hue d→Knobs p.g n)×C) :=
    fun i=>recenterQuery H o l s f S (x.1 i) x.2
  let Bad (x : (Hue d→Knobs p.g n)×C) :=
    ∃ u,weightsAff u ∧ P (compound p (repair x) u)
  have hμ:=pairW_law (sketch_law p n a hn) (unif_law (α:=C))
  have hp : pr μ Bad≤fiddleRate p (Hue d)*ε:=
    coherent_sketch_failure H o l s f S a hn P ε (hw l f)
  have hsub (x : (Hue d→Knobs p.g n)×C) (hx : μ x≠0)
      (hc : cellSlope (φ l) x.2=0) : Bad x := by
    have hx0 : sketchLaw p n a x.1≠0:=left_ne_zero_of_mul hx
    have hx' : sketchLaw p n a (repair x)≠0:=by
      rw [show sketchLaw p n a (repair x)=sketchLaw p n a x.1 from
        recenter_sketch_weight H o l s f S a x.1 x.2]
      exact hx0
    by_contra hbad
    change ¬∃ u,weightsAff u ∧ P (compound p (repair x) u) at hbad
    push Not at hbad
    let A:=incision p l s f (repair x)
    let Q:=pullM A A M
    let ψ:=libAug p l g (beamMap d) (drill p A o)
    have hgram : pullM A A (selfM p n m.mixM)=beamMap d :=
      (sketch_matrix p l s f m a hj (repair x) hx').trans ha
    have hcell (u : Vec (Hue d)) (hu : weightsAff u) :
        queryCell H o l s f (compound p (repair x) u)=x.2 := by
      rw [show compound p (repair x) u=
        recenterQuery H o l s f S (compound p x.1 u) x.2 from
          recenter_query_compound H o l s f S x.1 u hu x.2]
      exact recenter_query_cell H o l s f S hS' _ _
    have hpred (u : Vec (Hue d)) (hu : weightsAff u) :
        libPredict p l g (beamMap d) (drill p A o) u=φ l 0 x.2 := by
      unfold libPredict
      rw [lib_see p l s f (repair x) u hu o]
      rw [←star_primal_key o l s (lit f l (compound p (repair x) u)),hφ]
      change φ l (evmat (beamMap d) u u)
        (queryCell H o l s f (compound p (repair x) u))=φ l 0 x.2
      rw [hcell u hu,cell_affine (φ l),hc,zero_mul,add_zero]
    have harches : arches ψ=1 := by
      calc
        _=arches (fun u=>φ l 0 x.2+evmat (beamMap d) u u):=
          arches_affine_congr _ _ (fun u hu=>congrArg (·+evmat (beamMap d) u u) (hpred u hu))
        _=1:= (arches_constant_add _ _).trans (arches_beam d)
    have hval (u : Vec (Hue d)) (hu : weightsAff u) : ψ u=evmat Q u u := by
      let y:=compound p (repair x) u
      have hq : evmat (beamMap d) u u=dialed p l f y := by
        rw [←hgram]
        exact inc_diag p l s f m (repair x) u hu hj
      have hh : g l (dialed p l f y) (keyOne p l s (lit f l y) o)=
          dialed p l f y+evmat Q u u := by
        have hp0 : ¬P y:=hbad u hu
        have heq:=Eq.symm (not_ne_iff.mp hp0)
        refine heq.trans ((hm y (clean_compound E a hclean (repair x) hx' u)).trans ?_)
        rw [evmat_pull,inc_compound p l s f (repair x) u hu]
      change libPredict p l g (beamMap d) (drill p A o) u+evmat (beamMap d) u u=_
      unfold libPredict
      rw [lib_see p l s f (repair x) u hu o,hq,hh,add_right_comm,char_two,zero_add]
    have hrank:=(arches_rank ψ Q hval).trans
      (Nat.mul_le_mul_left 2 ((rank_lift_le ..).trans hM))
    rw [harches,Matrix.rank_one,Fintype.card_fin] at hrank
    omega
  have he : pr μ (fun x=>cellSlope (φ l) x.2=0)=pr unif (fun c=>cellSlope (φ l) c=0) := by
    simp only [pr,μ,pairW_avg]
    exact (sketch_law p n a hn).avg_const _
  rw [←he]
  exact (pr_mono_support μ hμ.nz hsub).trans hp

end
end Lax793645Proofs.Simplifications
