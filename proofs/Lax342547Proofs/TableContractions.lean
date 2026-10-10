import Lax342547.TableContractions
import Lax342547Proofs.TensorContractions

namespace Lax342547Proofs.TableContractions

open Lax342547.MomentSpace Lax342547.ExactPins Lax342547.ProjectedPins
open Lax342547.TableSpaces Lax342547.SmallTables Lax342547.TableContractions

theorem plus_extension {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (F : CrossForms Comp B H) (hF : Extends F T) (e : Comp) (i z : Fin 2) :
    (fullPlus F e i z).comp (projected P i (e, true)).subtype = plus T e i z := by
  classical
  ext v h
  exact hF.1 e (primalToTable P (e, true) i v) (tableChannel Q (e, false) z (Pi.single h 1))

theorem minus_extension {Comp B H N : Type} {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N}
    (T : Table P Q) (F : CrossForms Comp B H) (hF : Extends F T) (e : Comp) (i z : Fin 2) :
    (fullMinus F e i z).comp (projected P i (e, false)).subtype = minus T e i z := by
  classical
  ext v h
  exact hF.2 e (tableChannel Q (e, true) z (Pi.single h 1)) (primalToTable P (e, false) i v)

/--
---
conclusion: Lax342547.TableContractions.star_extension
---
The full channel maps restrict to the two table evaluations on the
projected primal factors. Extension independence of each tensor
contraction therefore gives equality on every effective component.
Summing gives the asserted identity on the entire effective profile.
-/
theorem star_extension {Comp B H N : Type} [Fintype Comp] [Fintype B] [Fintype H]
    {P Q : Pin (Comp × Bool) (Fin 2 × (B ⊕ H)) N} (T : Table P Q)
    (F : CrossForms Comp B H) (hF : Extends F T)
    (X : Submodule Binary (Comp → Matrix B B Binary)) (i z : Fin 2) (x : effective X P i) :
    starContraction T X i z x = fullContraction F X i z x.val := by
  simp only [starContraction, fullContraction, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply]
  apply Finset.sum_congr rfl
  intro e _
  exact TensorContractions.extension_agreement (plus T e i z) (minus T e i z)
    (fullPlus F e i z) (fullMinus F e i z) (plus_extension T F hF e i z)
    (minus_extension T F hF e i z) (component X P i e x)

end Lax342547Proofs.TableContractions
