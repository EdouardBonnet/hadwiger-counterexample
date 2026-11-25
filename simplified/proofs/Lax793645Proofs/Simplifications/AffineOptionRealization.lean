import Lax793645Proofs.Simplifications.AffineOptionContracts
import Lax793645Proofs.Simplifications.IndependentOptionLabels
import Lax793645Proofs.Simplifications.ScalablePlenitude

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis StatusAnalysis.Guild
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {n N r K : ℕ} {d e : Rates}

/-- These spaces depend on the pin plan, before any witnesses are selected. -/
structure PlanProtection (a : Plan p n) (q K : ℕ) where
  selector : Space (Vec (SelIdx p.b p.j))
  base : Space (Vec (AIdx p.g n))
  selector_dim : dim selector ≤ selectorProtectionDim p q K
  base_dim : dim base ≤ baseProtectionDim p K
  pin : ∀ i z,sPin a z i ≤ tensorCross selector base
  low : ∀ i z x,x ∈ sPin a z i → Matrix.rank (flattenMatrix.symm x) ≤ q →
    x ∈ tensorRectangle selector base

theorem plan_protection_exists (a : Plan p n) (q K : ℕ) (hK : planRank a ≤ K) :
    Nonempty (PlanProtection a q K) := by
  obtain ⟨U,V,hU,hV,hpin,hlow⟩ := affine_common_plan_protection a q K hK
  exact ⟨⟨U,V,hU,hV,hpin,hlow⟩⟩

theorem PlanProtection.protect_template {a : Plan p n} {q K : ℕ}
    (H : PlanProtection a q K) {I : Type} [Fintype I] [DecidableEq I]
    (v : Template p I)
    (hv : LinearIndependent F (H.selector.mkQ ∘ fun i => selV p.j (v.s i))) :
    affinePenSpace v a q K :=
  ⟨H.selector,H.base,H.selector_dim,H.base_dim,H.pin,H.low,hv⟩

set_option maxHeartbeats 1200000 in
theorem affine_optionVia (q : Format) (d e : Rates) (s t : Pin p n N)
    (T : Cross p n) (K : ℕ)
    (ha : tableInj s.sp t.sp T) (hb : tableInj t.sp s.sp (reciprocal p T))
    (tags : Tagging p (Messenger q)) (x : Charts p n d) (y : Charts p n e)
    (hx : charted x s.sp) (hy : charted y t.sp)
    (f : Fabric p q d true) (g : Fabric p q e false)
    (hf : affinePenSpace ((f.hang 0).pen tags) s.sp (affineQorth K) K)
    (hg : affinePenSpace ((g.hang 0).pen tags) t.sp (affineQorth K) K)
    (z : Messenger q → F) (hF : f.up tags z) (hG : g.up tags z)
    (hj : 1 ≤ p.J) (h2 : 2 ≤ p.g) (h₀ : ∀ i,1 ≤ q i ∧ q i ≤ 7)
    (he : speak _ _ (sendSum z f.amp g.amp)=(hailing p x y T,0)) :
    ∃ (a b : Script p (Messenger q)),
      AffineOptions.chances ⟨tags,z,f.hang a,g.hang b⟩ x y s t T K := by
  obtain ⟨hQ,hR,hL,hS⟩ := (spoken x y T z f.amp g.amp).mp he
  obtain ⟨a,ha'⟩ := proclaim_script true f.amp g.amp tags y (reciprocal p T) hR
    (fun i => (h₀ i).1) hS h2 hj
  have hh : rhyme g.amp f.amp := fun i => (add_comm ..).trans (hR i)
  obtain ⟨b,hb'⟩ := proclaim_script false g.amp f.amp tags x T hh
    (fun i => (h₀ i).1) hL h2 hj
  exact ⟨a,b,⟨h₀,hF,hG,hQ,hR,ha',hb'⟩,⟨hx,hf,hL,ha⟩,⟨hy,hg,hS,hb⟩⟩

set_option maxHeartbeats 1400000 in
/-- The strengthened scalar lists produce actual admissible numerical
options. Their protection is independent of the subsequently sampled inputs. -/
theorem affine_processions {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
    (A B : Stalls p) (η : ℝ) (a b : Pin p n N)
    (X : Charts p n d) (W : Charts p n e) (T : Cross p n)
    (hA : charted X a.sp) (hB : charted W b.sp)
    (ha : tableInj a.sp b.sp T) (hb : tableInj b.sp a.sp (reciprocal p T))
    (Pa : PlanProtection a.sp (affineQorth K) K)
    (Pb : PlanProtection b.sp (affineQorth K) K)
    (hg : 2 ≤ p.g) (hp : 1 ≤ p.J) (H : Straps (Label p.b))
    (hsupply : ∀ target : ∀ i,Suite d e i,
      (∀ i,target i ∈ chapter (stellar u s t η A B) H i) →
      ∃ f,IndependentParade (stellar u s t η A B)
        (fun side => if side then Pa.selector else Pb.selector) H target f Finset.univ)
    (hv : scorecard (chapter (stellar u s t η A B) H) (hailing p X W T)) :
    ∃ (q : Volumes) (g : Engagement p (toFormat q) d e)
      (s0 t0 : Script p (Messenger (toFormat q))),
      AffineOptions.chances (g.binding p s0 t0) X W a b T K ∧
        ∀ i : Messenger (toFormat q),η ≤ circlet u s t (g i).1 i.1 (g i).2 := by
  classical
  obtain ⟨target,htarget,hscalar⟩ := hv
  obtain ⟨f,hf⟩ := hsupply target htarget
  obtain ⟨q,g,hI,hG,hLI,hQ⟩ := independent_invite p u s t A B η _ target H f hf
  have hS (side : Bool) : Injective (fun i : Messenger (toFormat q) => (g i).1.s side) := by
    intro i j hij
    change (g i).1.s side=(g j).1.s side at hij
    apply (hLI side).injective
    change (if side then Pa.selector else Pb.selector).mkQ (selV p.j ((g i).1.s side))=
      (if side then Pa.selector else Pb.selector).mkQ (selV p.j ((g j).1.s side))
    rw [hij]
  let z := g.tags p
  let w := g.bits p
  let F0 := g.genre0 p
  let F1 := g.genre1 p
  have hM : F0.up z w ∧ F1.up z w := by
    constructor
    · exact ⟨hS true,fun i => (hG i).2.2.2.1.2.1,fun i => (hG i).2.2.2.1.1⟩
    exact ⟨hS false,fun i => (hG i).2.2.2.2.1.2.1,fun i => (hG i).2.2.2.2.1.1⟩
  have hPa : affinePenSpace ((F0.hang 0).pen z) a.sp (affineQorth K) K :=
    Pa.protect_template _ (hLI true)
  have hPb : affinePenSpace ((F1.hang 0).pen z) b.sp (affineQorth K) K :=
    Pb.protect_template _ (hLI false)
  obtain ⟨P,Q,hP⟩ := affine_optionVia (toFormat q) d e a b T K ha hb z X W hA hB F0 F1
    hPa hPb w hM.1 hM.2 hp hg hI (by
      have he : sendSum w F0.amp F1.amp=target := funext (fun i => hQ i)
      rw [he]
      exact hscalar)
  exact ⟨q,g,P,Q,hP,fun i => (hG i).2.2.2.2.2⟩

end
end Lax793645Proofs.Simplifications
