/- Replace pure block flavors by restrictions on finitely many tester
coordinates. All other coordinates retain their ordinary generic law. -/
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SyntheticArraySlices

namespace Lax793645Proofs.Simplifications
open Lax793645Proofs.Upstream.OAI.HadwigerCounterexample
open Finset Matrix Function
open scoped BigOperators
noncomputable section
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def retainedProbe (E : Finset (Tag p.g)) (i : ProbeIdx p.g) : Prop :=
  match i with
  | .inl (_,t) => t∉E
  | .inr _ => False

def cleanTicket (p : Shape) (E : Finset (Tag p.g)) (a : Tickets p) : Prop :=
  ∀ i, ¬retainedProbe E i → ∀ j b, a ((i,j),b)=0

def cleanInput (p : Shape) (E : Finset (Tag p.g)) (x : Knobs p.g n) : Prop :=
  cleanTicket p E (punchField p x)

theorem clean_scan (E : Finset (Tag p.g)) (x : Knobs p.g n)
    (h : cleanInput p E x) (l : Tag p.g) (i : ProbeIdx p.g) (hi : ¬retainedProbe E i) :
    scan p l Flavor.full x i=0 := by
  classical
  unfold scan
  split_ifs
  · unfold tested
    apply Finset.sum_eq_zero
    intro j _
    have hz := h i hi j true
    change zget (x (asBlock i)) (2*j.val)=0 at hz
    rw [hz,zero_mul]
  rfl

theorem sketch_issued (a : I → Tickets p) (x : I → Knobs p.g n)
    (h : sketchLaw p n a x≠0) (i : I) : punchField p (x i)=a i := by
  classical
  by_contra! hv
  refine h (Finset.prod_eq_zero (mem_univ i) (f:=fun i => rung p n (a i) (x i)) ?_)
  unfold rung
  rw [onW_val,ind_zero (show ¬issued p _ _ from hv),mul_zero,zero_div]

theorem punch_compound (x : I → Knobs p.g n) (u : Vec I) :
    punchField p (compound p x u)=∑ i,u i • punchField p (x i) := by
  classical
  funext j
  unfold punchField zget
  by_cases h : gaugeAddr p j<n
  · simp only [h, dif_pos, compound, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp [h]

theorem clean_compound (E : Finset (Tag p.g)) (a : I → Tickets p)
    (ha : ∀ i,cleanTicket p E (a i)) (x : I → Knobs p.g n)
    (hx : sketchLaw p n a x≠0) (u : Vec I) : cleanInput p E (compound p x u) := by
  intro i hi j b
  change punchField p (compound p x u) ((i,j),b)=0
  rw [punch_compound]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro k _
  rw [sketch_issued a x hx k,ha k i hi j b,mul_zero]

def retainedPunches (p : Shape) (l : Tag p.g) (E : Finset (Tag p.g)) : Finset (Punch p) := by
  classical
  exact Finset.univ.filter (fun i => usesPunch p l Flavor.full i ∧ retainedProbe E i.1)

theorem coordinate_tester_room (p : Shape) (l : Tag p.g) (E : Finset (Tag p.g)) :
    (privateWidth p.g)*(p.g-E.card)*p.r ≤ (retainedPunches p l E).card := by
  classical
  let u := Finset.univ.filter (fun i => allowed i l)
  let v := Finset.univ \ E
  let Z := u ×ˢ (v ×ˢ (Finset.univ : Finset (Fin p.r)))
  let f (i : Tag p.g × Tag p.g × Fin p.r) : Punch p := (.inl (i.1,i.2.1),i.2.2)
  have hf : Injective f := by
    rintro ⟨i,j,k⟩ ⟨x,y,z⟩ h
    simpa only [Prod.mk.injEq,Sum.inl.injEq,f,and_assoc] using h
  have he : Z.image f ⊆ retainedPunches p l E := by
    rintro i hi
    obtain ⟨⟨i,j,k⟩,hv,rfl⟩ := mem_image.mp hi
    simp only [Z,u,v,mem_product,mem_sdiff,mem_filter,mem_univ,true_and,and_true] at hv
    exact mem_filter.mpr ⟨mem_univ _,hv.1,hv.2⟩
  have ht := card_le_card he
  rw [card_image_of_injective _ hf] at ht
  have hu : u.card=privateWidth p.g := by
    have h := card_allowed' l
    rw [Fintype.card_subtype] at h
    exact h
  refine le_trans ?_ ht
  unfold Z v
  rw [card_product,card_product,Finset.card_sdiff_of_subset (subset_univ _),
    card_univ,card_univ,hu,Fintype.card_fin,Fintype.card_fin,mul_assoc]

omit [DecidableEq I] in
set_option maxHeartbeats 1000000 in
theorem masked_punch_real (p : Shape) (l : Tag p.g) (E : Finset (Tag p.g)) (G : Mat I I)
    (h : G.rank ≤ (retainedPunches p l E).card) :
    ∃ a : I → Tickets p, labGram p l Flavor.full a=G ∧ ∀ i,cleanTicket p E (a i) := by
  classical
  let P := retainedPunches p l E
  let q := Fintype.equivFinOfCardEq (Fintype.card_coe P)
  obtain ⟨u,v,hg⟩ := mul_factor G P.card h
  let x (i:I) (j:Punch p) := if h:j∈P then u i (q ⟨j,h⟩) else 0
  let y (i:I) (j:Punch p) := if h:j∈P then v (q ⟨j,h⟩) i else 0
  let a (i:I) : Tickets p := fun j => if j.2 then x i j.1 else y i j.1
  refine ⟨a,?_,?_⟩
  · rw [←hg]
    ext i j
    change (∑ t:Punch p, (if usesPunch p l Flavor.full t then a i (t,true)*a j (t,false) else 0)) =
      ∑ t,u i t*v t j
    have he (t : Punch p) :
        (if usesPunch p l Flavor.full t then a i (t,true)*a j (t,false) else 0) =
        if t∈P then x i t*y j t else 0 := by
      by_cases ht : t∈P
      · have hp : usesPunch p l Flavor.full t := (mem_filter.mp ht).2.1
        simp only [ht,hp,ite_true,a,Bool.true_eq_false,Bool.false_eq_true,ite_false]
      have hx : x i t=0 := dif_neg ht
      have hy : y j t=0 := dif_neg ht
      simp [a,ht,hx,hy]
    simp_rw [he]
    rw [←Finset.sum_filter]
    rw [show Finset.univ.filter (fun t => t∈P)=P from by ext t; simp]
    change ∑ t∈P,x i t*y j t=_
    calc _ = ∑ t:P,x i t.val*y j t.val := (Finset.sum_coe_sort P _).symm
         _ = _ := by
          have hh (t : P) : x i t.val*y j t.val=u i (q t)*v (q t) j := by
            unfold x y
            rw [dif_pos t.property,dif_pos t.property]
          simp_rw [hh]
          exact Equiv.sum_comp q (fun t => u i t*v t j)
  intro i j hj k b
  have ht : (j,k)∉P := fun h => hj (mem_filter.mp h).2.2
  cases b <;> simp [a,x,y,ht]

end
end Lax793645Proofs.Simplifications
