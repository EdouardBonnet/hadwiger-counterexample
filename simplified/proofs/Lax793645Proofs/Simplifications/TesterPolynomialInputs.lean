import Lax793645Proofs.Simplifications.OnePolynomialInputs
import Lax793645Proofs.Simplifications.PolynomialFixedAccuracy
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.TesterSummaryMass
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ProductCoordinateReplacement

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Function Finset
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {p : Shape} {n : ℕ}

theorem dialed_update_shared (l : Tag p.g) (f : Flavor p.g)
    (x : Knobs p.g n) (z : Vec (Fin n)) :
    dialed p l f (update x Block.S z)=(scan p l f x).diagO+tested p.r z := by
  classical
  unfold dialed Digest.sumBit Digest.diagO scan
  cases f <;> simp [Flavor.keeps,asBlock,Block.O,Block.S]

theorem dialed_bit_mass (l : Tag p.g) (f : Flavor p.g)
    (hr : 1≤p.r) (hn : 2*p.r≤n) (b : F) :
    (1/4:ℝ)≤pr (spins p n) (fun x=>dialed p l f x=b) := by
  have he : pr (spins p n) (fun x=>dialed p l f x=b)=
      avg (spins p n) (fun x=>pr unif (fun z=>dialed p l f (update x Block.S z)=b)) := by
    exact update_avg (fun _ : Block p.g=>unif) Block.S _ unif_law
  rw [he]
  apply (spins_law p n).le_avg
  intro x
  have heq : (fun z=>dialed p l f (update x Block.S z)=b)=
      (fun z=>tested p.r z=b-(scan p l f x).diagO) := by
    funext z
    rw [dialed_update_shared]
    apply propext
    rw [eq_sub_iff_add_eq,add_comm]
  rw [heq]
  exact tested_fraction p.r n hr hn _

theorem tested_single_pair (hr : 1≤p.r) (hn : 2*p.r≤n) (a b : F) :
    tested p.r (Pi.single (⟨0,by omega⟩:Fin n) a+
      Pi.single (⟨1,by omega⟩:Fin n) b)=a*b := by
  classical
  unfold tested
  rw [Finset.sum_eq_single (⟨0,hr⟩:Fin p.r)]
  · simp [zget,show 0<n by omega,show 1<n by omega]
  · intro i _ hi
    have hi' : i.val≠0 := fun h=>hi (Fin.ext h)
    have h0 : 2*i.val<n := by omega
    have h1 : 2*i.val+1<n := by omega
    simp only [zget,dif_pos h0,dif_pos h1,Pi.add_apply]
    have ha : (⟨2*i.val,h0⟩:Fin n)≠⟨0,by omega⟩ := by
      intro h; have hh := congrArg Fin.val h; simp only [Fin.mk_val] at hh; omega
    have hb : (⟨2*i.val,h0⟩:Fin n)≠⟨1,by omega⟩ := by
      intro h; have hh := congrArg Fin.val h; simp only [Fin.mk_val] at hh; omega
    simp [Pi.single_eq_of_ne ha,Pi.single_eq_of_ne hb]
  · simp

theorem dialed_tester_directions (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (hr : 1≤p.r) (hn : 2*p.r≤n) :
    ∃ a b : Base p.g n,∀ y,
      dialed p l f (flattenKnobs p n (y+a+b))-
      dialed p l f (flattenKnobs p n (y+a))-
      dialed p l f (flattenKnobs p n (y+b))+
      dialed p l f (flattenKnobs p n y)=1 := by
  classical
  let x (a b : F) : Knobs p.g n:=Pi.single Block.S
    (Pi.single (⟨0,by omega⟩:Fin n) a+Pi.single (⟨1,by omega⟩:Fin n) b)
  have hx (a b : F) : dialed p l f (x a b)=a*b := by
    have he : x a b=update (0:Knobs p.g n) Block.S
        (Pi.single (⟨0,by omega⟩:Fin n) a+Pi.single (⟨1,by omega⟩:Fin n) b) := by
      funext B
      by_cases h : B=Block.S <;> simp [x,h]
    rw [he,dialed_update_shared,tested_single_pair hr hn]
    simp [Digest.diagO,scan,tested,zget]
  let a:=(flattenKnobs p n).symm (x 1 0)
  let b:=(flattenKnobs p n).symm (x 0 1)
  refine ⟨a,b,quadratic_second_difference _ (one_input_tester_quadratic l s f) a b ?_⟩
  have hab : flattenKnobs p n (a+b)=x 1 1 := by
    rw [map_add]
    change x 1 0+x 0 1=x 1 1
    simp only [x,Pi.single_zero,add_zero,zero_add,Pi.single_add]
  rw [hab]
  change dialed p l f (x 1 1)-dialed p l f (x 1 0)-dialed p l f (x 0 1)+
    dialed p l f 0=1
  have hzero : (0:Knobs p.g n)=x 0 0 := by simp [x]
  rw [hzero,hx,hx,hx,hx]
  norm_num

end
end Lax793645Proofs.Simplifications
