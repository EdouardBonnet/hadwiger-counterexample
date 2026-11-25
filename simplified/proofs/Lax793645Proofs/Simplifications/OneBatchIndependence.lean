import Lax793645Proofs.Simplifications.QuadraticBatchIndependence
import Lax793645Proofs.Simplifications.OneIndependentImages

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
  [DecidableEq I] [DecidableEq J] [DecidableEq G] {p : Shape} {n N : ℕ}
variable {f : Route I G}

theorem one_frame_images (g : Route I G) (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3≤N)
    (A : NomQuery p n g) (hA : ∀ i,Injective (A i).mulVec) :
    mapW (oneForumLaw m N) (onePeek g A)=quadraticStation (database m A A) N := by
  rw [one_law_peek g m hN]
  unfold quadraticStation
  congr 1
  funext x
  apply propext
  apply forall_congr'
  intro i
  have hk : (A i).mulVecLin.ker=⊥:=LinearMap.ker_eq_bot.mpr (hA i)
  change (_=_ ∧ _) ↔ (Injective _ ∧ _)
  rw [hk,LinearMap.ker_eq_bot]
  rfl

set_option maxHeartbeats 800000 in
theorem one_pooled_batch (A : J → NomQuery p n f) (m : Mixer p n)
    (hN : Fintype.card (Row p n)+2*p.h+3≤N)
    (k : ℝ) (hk : ∀ i,num (Port (tied f J) i)≤k)
    (hL : 2*k+2≤(N:ℝ))
    (ha : ∀ i, Injective (pooled A i).mulVec)
    (F : J→ Wgt (Rack I N)) (hf : ∀ i x,|F i x|≤1) :
    let w := oneForumLaw (G:=G) m N
    |avg w (fun x => ∏ i, F i (onePeek f (A i) x)) -
      ∏ i, avg w (fun x => F i (onePeek f (A i) x))|≤
      2*quadraticNetFact (tied f J)*twinkle (tied f J) k N := by
  classical
  let w := oneForumLaw m N (G:=G)
  let Z := database m (pooled A) (pooled A)
  have he i :
      avg w (fun x => F i (onePeek f (A i) x))=
        avg (quadraticStation (database m (A i) (A i)) N) (F i) := by
    unfold w; rw [←mapW_avg,one_frame_images f m hN (A i) (pool_injective ha i)]
  have hx :
      avg w (fun x => ∏ i, F i (onePeek f (A i) x)) =
        avg (quadraticStation Z N) (brightProd F) := by
    rw [←one_frame_images (tied f J) m hN (pooled A) ha,mapW_avg]
    refine avg_congr fun x _=>?_ 
    simp_rw [brightProd,one_peek_pooled]

  dsimp only
  change |avg w _ - ∏ i, avg w _| ≤ _
  simp_rw [he]; rw [hx]
  have hi := quadratic_compare_lanes Z F hf k hk (fun i => by linarith only [hk i,hL])
  simp_rw [Z,lane_pooled] at *
  exact hi

end
end Lax793645Proofs.Simplifications
