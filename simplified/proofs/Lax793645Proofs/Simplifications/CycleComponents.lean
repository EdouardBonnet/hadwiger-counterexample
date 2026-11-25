import Lax793645Proofs.Simplifications.CycleMatchings
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-! Finite component indices for the cycle replacement.  The cases with fewer
than three tags are included so that the dimension API remains total. -/
namespace Lax793645Proofs.Simplifications.CycleGeometry
open scoped BigOperators
noncomputable section

abbrev Tag := Fin
abbrev Comp (g : ℕ) :=
  {e : Tag g × Tag g // e.1 < e.2 ∧ (SimpleGraph.cycleGraph g).Adj e.1 e.2}

def degree (g : ℕ) := min 2 (g-1)

def edge {g : ℕ} (l d : Tag g) (h : (SimpleGraph.cycleGraph g).Adj l d) : Comp g :=
  if hl : l < d then ⟨(l,d),hl,h⟩ else
    ⟨(d,l),lt_of_le_of_ne (le_of_not_gt hl) h.ne.symm,h.symm⟩

theorem edge_eq {g : ℕ} {l d : Tag g} (h : l < d)
    (ha : (SimpleGraph.cycleGraph g).Adj l d) : edge l d ha=⟨(l,d),h,ha⟩ := by
  simp [edge,h]

theorem edge_symm {g : ℕ} {l d : Tag g} (h : (SimpleGraph.cycleGraph g).Adj l d) :
    edge l d h=edge d l h.symm := by
  rcases lt_or_gt_of_ne h.ne with e|e
  · simp [edge,e,not_lt.mpr e.le]
  · simp [edge,e,not_lt.mpr e.le]

def inc {g : ℕ} (e : Comp g) (l : Tag g) := e.val.1=l ∨ e.val.2=l
instance {g : ℕ} (e : Comp g) (l : Tag g) : Decidable (inc e l) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem inc_edge_iff {g : ℕ} {l d x : Tag g} (h : (SimpleGraph.cycleGraph g).Adj l d) :
    inc (edge l d h) x ↔ l=x ∨ d=x := by
  by_cases e : l<d <;> simp [inc,edge,e,or_comm]

abbrev Star {g : ℕ} (l : Tag g) := {e : Comp g // inc e l}

def starEquiv {g : ℕ} (l : Tag g) : (SimpleGraph.cycleGraph g).neighborSet l ≃ Star l := by
  let f (d : (SimpleGraph.cycleGraph g).neighborSet l) : Star l :=
    ⟨edge l d d.property,(inc_edge_iff _).mpr (Or.inl rfl)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    have hi : inc (edge l i i.property) i := (inc_edge_iff _).mpr (Or.inr rfl)
    change inc (f i).val i at hi
    rw [h] at hi
    exact Subtype.ext (((inc_edge_iff j.property).mp hi).resolve_left i.property.ne).symm
  · rintro ⟨⟨⟨i,j⟩,hij,hA⟩,he⟩
    rcases he with he|he
    · change i=l at he
      subst l
      exact ⟨⟨j,hA⟩,Subtype.ext (edge_eq hij hA)⟩
    · change j=l at he
      subst l
      refine ⟨⟨i,hA.symm⟩,Subtype.ext ?_⟩
      change edge j i hA.symm=_
      rw [edge_symm,edge_eq hij hA]

theorem card_star {g : ℕ} (l : Tag g) : Fintype.card (Star l)=degree g := by
  rw [←Fintype.card_congr (starEquiv l),SimpleGraph.card_neighborSet_eq_degree]
  match g with
  | 0 => exact Fin.elim0 l
  | 1 => simp [SimpleGraph.cycleGraph_one_eq_bot,degree]
  | 2 => rw [SimpleGraph.cycleGraph_degree_two_le]; fin_cases l <;> decide
  | k+3 => rw [SimpleGraph.cycleGraph_degree_three_le]; simp [degree]

theorem card_star_le {g : ℕ} (l : Tag g) : Fintype.card (Star l)≤2 := by
  rw [card_star]; exact min_le_left _ _

theorem degree_of_three_le {g : ℕ} (h : 3≤g) : degree g=2 := by
  unfold degree; omega

def next {g : ℕ} (l : Tag g) : Tag g :=
  ⟨(l.val+1)%g,Nat.mod_lt _ (by have := l.isLt; omega)⟩

theorem next_eq_add {g : ℕ} [NeZero g] (l : Tag g) : next l=l+1 := by
  apply Fin.ext
  simp [next,Fin.val_add,Nat.add_mod_mod]

theorem adjacent_next {g : ℕ} (hg : 2≤g) (l : Tag g) :
    (SimpleGraph.cycleGraph g).Adj l (next l) := by
  rcases g with _|_|k
  · omega
  · omega
  rw [next_eq_add,SimpleGraph.cycleGraph_adj]
  exact Or.inr (add_sub_cancel_left l 1)

def forward {g : ℕ} (hg : 2≤g) (l : Tag g) : Comp g := edge l (next l) (adjacent_next hg l)

theorem inc_forward {g : ℕ} (hg : 2≤g) (l t : Tag g) :
    inc (forward hg l) t ↔ l=t ∨ next l=t := inc_edge_iff _

theorem forward_injective {g : ℕ} (hg : 3≤g) : Function.Injective (forward (by omega : 2≤g)) := by
  have : NeZero g := ⟨by omega⟩
  intro l d he
  have h1 : inc (forward (by omega : 2≤g) d) l := by
    rw [←he]; exact (inc_forward _ _ _).mpr (Or.inl rfl)
  have h2 : inc (forward (by omega : 2≤g) d) (next l) := by
    rw [←he]; exact (inc_forward _ _ _).mpr (Or.inr rfl)
  rcases (inc_forward _ _ _).mp h1 with h|h
  · exact h.symm
  rcases (inc_forward _ _ _).mp h2 with h'|h'
  · simp only [next_eq_add] at h h'
    have hx : d+1+1=d := by rw [h,←h']
    have hx' : d+(1+1)=d+0 := by simpa only [add_assoc,add_zero] using hx
    have hz := congrArg Fin.val (add_left_cancel hx')
    change (1%g+1%g)%g=0 at hz
    rw [Nat.mod_eq_of_lt (by omega : 1<g),Nat.mod_eq_of_lt (by omega : 1+1<g)] at hz
    omega
  simp only [next_eq_add] at h'
  exact add_right_cancel h'.symm

theorem forward_surjective {g : ℕ} (hg : 2≤g) : Function.Surjective (forward hg) := by
  rcases g with _|_|k
  · omega
  · omega
  rintro ⟨⟨l,d⟩,hlt,ha⟩
  rcases SimpleGraph.cycleGraph_adj.mp ha with h|h
  · have hd : next d=l := by rw [next_eq_add]; simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm
    refine ⟨d,?_⟩
    unfold forward
    simp only [hd]
    rw [edge_symm,edge_eq hlt]
  · have hl : next l=d := by rw [next_eq_add]; simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm
    refine ⟨l,?_⟩
    unfold forward
    simp only [hl]
    rw [edge_eq hlt]

def forwardEquiv {g : ℕ} (hg : 3≤g) : Tag g ≃ Comp g :=
  Equiv.ofBijective (forward (by omega : 2≤g))
    ⟨forward_injective hg,forward_surjective (by omega)⟩

theorem card_comp {g : ℕ} (hg : 3≤g) : Fintype.card (Comp g)=g :=
  (Fintype.card_congr (forwardEquiv hg)).symm.trans (Fintype.card_fin g)

def cut {g : ℕ} {V : Type*} [Add V] (w : Tag g → V) (e : Comp g) :=
  w e.val.1+w e.val.2

theorem cut_forward {g : ℕ} {V : Type*} [AddCommMonoid V]
    (hg : 2≤g) (w : Tag g → V) (l : Tag g) :
    cut w (forward hg l)=w l+w (next l) := by
  unfold cut forward edge
  split <;> simp only <;> first | rfl | exact add_comm _ _

theorem cut_sum {g : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (hg : 3≤g) (w : Tag g → V) : ∑ e, cut w e=0 := by
  rw [←(forwardEquiv hg).sum_comp]
  change (∑ l,cut w (forward (by omega : 2≤g) l))=0
  simp_rw [cut_forward,Finset.sum_add_distrib]
  have : NeZero g := ⟨by omega⟩
  simp only [next_eq_add]
  have he : (∑ l:Fin g,w (l+1))=∑ l,w l :=
    Equiv.sum_comp (Equiv.addRight (1:Fin g)) w
  rw [he]
  calc
    _ = (1+1 : ZMod 2) • (∑ l,w l) := by rw [add_smul,one_smul]
    _ = 0 := by rw [CharTwo.add_self_eq_zero (1 : ZMod 2),zero_smul]

/-- Two incident coefficients agree when their sum is the cycle relation. -/
theorem star_constant {g : ℕ} (a : Comp g → ZMod 2) (l : Tag g)
    (hzero : ∀ e,¬inc e l → a e=0) (hsum : 3≤g → ∑ e,a e=0) :
    ∃ c : ZMod 2,∀ e,a e=if inc e l then c else 0 := by
  classical
  have hsame (e e' : Comp g) (he : inc e l) (he' : inc e' l) :
      a e=a e' := by
    by_cases hh : e=e'
    · rw [hh]
    let T : Finset (Comp g) := Finset.univ.filter (fun d => inc d l)
    have hTc : T.card=degree g := by
      simpa only [Star,Fintype.card_subtype] using card_star l
    have hpair : ({e,e'}:Finset (Comp g)).card=2 := by simp [hh]
    have hsub : ({e,e'}:Finset (Comp g)) ⊆ T := by
      intro d hd
      have hd' : d=e ∨ d=e' := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hd
      rcases hd' with rfl|rfl <;> simp [T,he,he']
    have htwo : 2≤degree g := by rw [←hTc,←hpair]; exact Finset.card_le_card hsub
    have hg : 3≤g := by have := htwo.trans (min_le_right 2 (g-1)); omega
    have hT : ({e,e'}:Finset (Comp g))=T :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hTc,degree_of_three_le hg,hpair])
    have hsum : a e+a e'=0 := by
      calc
        _ = ∑ d∈({e,e'}:Finset (Comp g)),a d := by simp [hh]
        _ = ∑ d,a d := Finset.sum_subset (Finset.subset_univ _) (by
          intro d _ hd
          apply hzero d
          intro hc
          exact hd (hT ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩)))
        _ = 0 := hsum hg
    exact add_right_cancel (hsum.trans (CharTwo.add_self_eq_zero (a e')).symm)
  by_cases h : ∃ e,inc e l
  · obtain ⟨e,he⟩ := h
    refine ⟨a e,fun d => ?_⟩
    by_cases hd : inc d l
    · rw [if_pos hd]; exact hsame d e hd he
    · rw [if_neg hd]; exact hzero d hd
  refine ⟨0,fun e => ?_⟩
  have he : ¬inc e l := fun he => h ⟨e,he⟩
  rw [if_neg he,hzero e he]

/-- The two selected coefficients at a tag agree by the one cycle relation. -/
theorem cut_star_constant {g : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (w : Tag g → V) (l : Tag g) (f : V →ₗ[ZMod 2] ZMod 2)
    (hzero : ∀ e, ¬inc e l → f (cut w e)=0) :
    ∃ c : ZMod 2, ∀ e, f (cut w e)=if inc e l then c else 0 :=
  star_constant (fun e => f (cut w e)) l hzero (fun hg => by rw [←map_sum,cut_sum hg,map_zero])

/-- A total outgoing projection, including the empty one-tag geometry. -/
def outgoingMap {g : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (l : Tag g) : (Comp g → V) →ₗ[ZMod 2] V :=
  if hg : 2≤g then LinearMap.proj (forward hg l) else 0

theorem outgoingMap_cut {g : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (w : Tag g → V) (l : Tag g) : outgoingMap l (cut w)=w l+w (next l) := by
  classical
  by_cases hg : 2≤g
  · rw [outgoingMap,dif_pos hg]; exact cut_forward hg w l
  have he : g=1 := by have := l.isLt; omega
  subst g
  have hl : next l=l := Subsingleton.elim _ _
  rw [outgoingMap,dif_neg hg,LinearMap.zero_apply,hl]
  symm
  calc
    _ = (1+1 : ZMod 2) • w l := by rw [add_smul,one_smul]
    _ = 0 := by rw [CharTwo.add_self_eq_zero (1 : ZMod 2),zero_smul]

/-- The starting vertex of an edge in the matching obtained by deleting t. -/
def matchingVertex {g : ℕ} (t : Tag g) (i : Fin ((g-1)/2)) : Tag g :=
  ⟨2*i.val+1,by have := i.isLt; omega⟩+t

def matchingMap {g : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (t : Tag g) : (Comp g → V) →ₗ[ZMod 2] V :=
  ∑ i : Fin ((g-1)/2),outgoingMap (matchingVertex t i)

theorem matchingMap_cut {g : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (hg : Odd g) (w : Tag g → V) (t : Tag g) :
    matchingMap t (cut w)=(∑ l,w l)+w t := by
  classical
  obtain ⟨r,hr⟩ := hg
  have he : g=2*r+1 := by omega
  subst g
  unfold matchingMap
  simp only [LinearMap.sum_apply,outgoingMap_cut,next_eq_add]
  have half : (2*r+1-1)/2=r := by omega
  rw [←Equiv.sum_comp (finCongr half).symm]
  change (∑ i:Fin r,(w (matchingEdge t i)+w (matchingEdge t i+1)))=_
  rw [matching_covers,Fintype.sum_eq_add_sum_subtype_ne w t,add_right_comm]
  have hz : w t+w t=0 := by
    calc
      _ = (1+1 : ZMod 2) • w t := by rw [add_smul,one_smul]
      _ = 0 := by rw [CharTwo.add_self_eq_zero (1 : ZMod 2),zero_smul]
  rw [hz,zero_add]

end
end Lax793645Proofs.Simplifications.CycleGeometry
