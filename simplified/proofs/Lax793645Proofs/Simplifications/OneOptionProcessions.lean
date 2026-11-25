import Lax793645Proofs.Simplifications.OneOptionProtection

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open StatusAnalysis StatusAnalysis.DualAnalysis StatusAnalysis.Guild
open Matrix LinearMap Submodule Module Finset Function
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {n N r K : ℕ} {d e : Rates}

set_option maxHeartbeats 1400000 in
/-- The strengthened scalar lists produce actual admissible numerical
options. Their protection is independent of the subsequently sampled inputs. -/
theorem one_processions {u : Terrain p r} {s : Gazette p r d} {t : Gazette p r e}
    (A B : Stalls p) (η : ℝ) (a b : ImagePin (Comp p.g) (OneColumn p n) (2*N))
    (X : Charts p n d) (W : Charts p n e) (T : OneCross p n)
    (hA : oneCharted X a.sp) (hB : oneCharted W b.sp)
    (ha : oneTableSafe a.sp b.sp T) (hb : oneTableSafe b.sp a.sp (fun e=>(T e)ᵀ))
    (Pa : OnePlanProtection a.sp K)
    (Pb : OnePlanProtection b.sp K)
    (hg : 3 ≤ p.g) (hodd : Odd p.g) (hp : 1 ≤ p.J) (H : Straps (Label p.b))
    (hsupply : ∀ target : ∀ i,Suite d e i,
      (∀ i,target i ∈ chapter (stellar u s t η A B) H i) →
      ∃ f,IndependentParade (stellar u s t η A B)
        (fun side => if side then Pa.selector else Pb.selector) H target f Finset.univ)
    (hv : scorecard (chapter (stellar u s t η A B) H) (oneHailing X W T)) :
    ∃ (q : Volumes) (g : Engagement p (toFormat q) d e)
      (s0 t0 : Script p (Messenger (toFormat q))),
      OneOptions.chances (g.binding p s0 t0) X W a b T K ∧
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
  have hPa : OnePenSpace ((F0.hang 0).pen z) a.sp K :=
    Pa.protect_template _ (one_messenger_card (p:=p) (n:=n) hI) (hLI true)
  have hPb : OnePenSpace ((F1.hang 0).pen z) b.sp K :=
    Pb.protect_template _ (one_messenger_card (p:=p) (n:=n) hI) (hLI false)
  obtain ⟨P,Q,hP⟩ := OneOptions.optionVia (toFormat q) d e a b T K ha hb z X W hA hB F0 F1
    hPa hPb w hM.1 hM.2 hp hg hodd hI (by
      have he : sendSum w F0.amp F1.amp=target := funext (fun i => hQ i)
      rw [he]
      exact hscalar)
  exact ⟨q,g,P,Q,hP,fun i => (hG i).2.2.2.2.2⟩

end
end Lax793645Proofs.Simplifications
