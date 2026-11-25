import Lax793645Proofs.Simplifications.ReducedMixers

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Matrix LinearMap Function Finset
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {p : Shape} {I : Type}

theorem cycle_mixer_usable (hg : 3≤p.g) (l d : Tag p.g) :
    ∃ e : Comp p.g,inc e l ∧cycleOrigin e≠d := by
  haveI : NeZero p.g:=⟨by omega⟩
  by_cases he:l=d
  · subst d
    let t : Tag p.g:=l-1
    have ht:CycleGeometry.next t=l:=by rw [CycleGeometry.next_eq_add]; exact sub_add_cancel _ _
    have hn:t≠l:=by
      have hn: t≠CycleGeometry.next t:=(CycleGeometry.adjacent_next (by omega) t).ne
      rwa [ht] at hn
    exact ⟨CycleGeometry.forward (by omega) t,
      (CycleGeometry.inc_forward _ _ _).mpr (Or.inr ht),by rwa [cycle_origin_forward hg]⟩
  exact ⟨CycleGeometry.forward (by omega) l,
    (CycleGeometry.inc_forward _ _ _).mpr (Or.inl rfl),by rwa [cycle_origin_forward hg]⟩

theorem prescribedB_reduced (hg : Odd p.g) (t : Tagging p I) (s : Script p I) (x y : I) :
    prescribedB p t (reducedScript s) x y=
      ∑ j : Fin p.J,∑ e : Comp p.g,if inc e (t x) ∧cycleOrigin e≠t y then
        s x y (reducedSlot ((j,e),true))*s x y (reducedSlot ((j,e),false)) else 0 := by
  unfold prescribedB
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro e _
  by_cases he:inc e (t x)
  · have hh:=congrArg (fun a:F=>a*(s x y (reducedSlot ((j,e),true))*
        s x y (reducedSlot ((j,e),false)))) (cycle_weight_star hg e (t y))
    simp only [sum_mul,ite_mul,zero_mul] at hh
    have hf:(∑ f:Comp p.g,if inc e (t x) ∧inc f (t y) then
        reducedScript s x y ((j,e,f),true)*reducedScript s x y ((j,e,f),false) else 0)=
        ∑ f:Comp p.g,if inc f (t y) then cycleWeight e f*
          (s x y (reducedSlot ((j,e),true))*s x y (reducedSlot ((j,e),false))) else 0 := by
      apply sum_congr rfl
      intro f _
      by_cases h:inc f (t y) <;> simp [reducedScript,reducedSlot,he,h,mul_assoc]
    rw [hf,hh]
    by_cases h:cycleOrigin e=t y <;> simp [he,h]
  simp [he]

theorem reduced_scripted (hg : 3≤p.g) (hodd : Odd p.g) (hJ : 1≤p.J)
    (t : Tagging p I) (g : I→I→F) :
    ∃ s : Script p I,∀ x y,prescribedB p t (reducedScript s) x y=g x y := by
  choose q hq using fun x y : I=>cycle_mixer_usable hg (t x) (t y)
  let j0 : Fin p.J:=⟨0,hJ⟩
  let s : Script p I:=fun x y i=>
    if i.1.1=j0 ∧i.1.2.1=q x y then if i.2 then g x y else 1 else 0
  refine ⟨s,fun x y=>?_⟩
  rw [prescribedB_reduced hodd,sum_eq_single j0]
  · rw [sum_eq_single (q x y)]
    · simp [s,reducedSlot,(hq x y).1,(hq x y).2]
    · intro e _ he
      simp [s,reducedSlot,he]
    simp
  · intro j _ hj
    simp [s,reducedSlot,hj]
  simp

variable [Fintype I]

/-- Every scalar prescription can be met using only the independent mixer
bits. The full script array is just a deterministic expansion of those bits. -/
theorem choose_reduced_script (p : Shape) (t : Tagging p I) (a b : I→Bool)
    (d f d' : Vec I)
    (h : ∀ i : Bool,(∑ x∈aiming a b i true,(d' x+f x))=
      ∑ x∈aiming a b i false,(d' x+f x))
    (ha : ∀ i j : Bool,∑ x∈aiming a b i j,(d x+d' x)=1)
    (hc : ∀ i j : Bool,(aiming a b i j).Nonempty)
    (u : Mat I I) (hu : uᵀ=u) (hg : 3≤p.g) (hodd : Odd p.g) (hJ : 1≤p.J) :
    ∃ s : Script p I,fulfills p t d f u (reducedScript s) a b := by
  obtain ⟨s,hs⟩:=choose_script p t a b d f d' h ha hc u hu (by omega) hJ
  obtain ⟨r,hr⟩:=reduced_scripted hg hodd hJ t (prescribedB p t s)
  refine ⟨r,fun x j=>?_⟩
  simpa only [prescribedT,hr] using hs x j

end
end Lax793645Proofs.Simplifications
