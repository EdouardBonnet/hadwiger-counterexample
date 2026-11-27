import Lax793645Proofs.Simplifications.MatchingNeighborhoods
import Lax793645Proofs.Simplifications.OrderedSlotCompletion
import Lax793645Proofs.Simplifications.MatchingTransfer
import Lax793645Proofs.Simplifications.SymmetricBlockCompletion
import Lax793645Proofs.Construction
import Lax793645Proofs.FiniteScores
import Lax793645Proofs.FractionalCounterexample
import Lax793645Proofs.FractionalColoring
import Lax793645Proofs.HadwigerMatching.MinorBound
import Lean.Util.CollectAxioms

/-!
Check the original construction and its ordinary and fractional consequences.
Close archive statement references with their kernel-checked proofs, then
inspect each theorem's actual dependencies and axioms. From proofs/, run

    lake build
    lake env lean ../verification/neighborhoods-and-gram-patterns.lean
-/
namespace HadwigerVerification
open Lean Elab.Command

private abbrev Renamings := Std.HashMap Name Name

private def localName (n : Name) : Bool :=
  (`Lax793645Proofs).isPrefixOf (privateToUserName n) ||
  (`Lax793645).isPrefixOf (privateToUserName n) ||
  (`HadwigerVerification).isPrefixOf n

private partial def rebuild (n : Name) : StateT Renamings CoreM Name := do
  unless localName n do return n
  if let some name := (← get)[n]? then return name
  modify (·.insert n n)
  let info ← getConstInfo n
  let some value := info.value? (allowOpaque := true) | return n
  for key in value.getUsedConstants do let _ ← rebuild key
  let names ← get
  let newValue := value.replace fun
    | .const k ls => do
        let dst ← names[k]?
        guard (k != dst)
        return .const dst ls
    | _ => none
  if value == newValue then return n
  let dst := `HadwigerVerification.Replayed ++ n
  match info with
  | .thmInfo v =>
    addDecl (.thmDecl {v with name := dst, value := newValue, all := [dst]})
  | .defnInfo v =>
    addDecl (.defnDecl {v with name := dst, value := newValue, all := [dst]})
  | _ => throwError "Unexpected declaration on the changed proof path: {n}"
  modify (·.insert n dst)
  return dst

private partial def dependencies (n : Name) : StateT NameSet CoreM Unit := do
  unless localName n do return
  if (← get).contains n then return
  modify (·.insert n)
  let c ← getConstInfo n
  for k in c.getUsedConstantsAsSet do dependencies k

open Lax793645Proofs.Simplifications Lax793645Proofs.Upstream.OAI.HadwigerCounterexample

set_option maxHeartbeats 0 in
run_cmd liftCoreM do
  let oldGraph := ``matching_exposure_transfer
  let newGraph := ``MatchingNeighborhoods.matching_certificate_transfer
  let oldGram := ``symmetric_patterned_block_completion
  let newGram := ``ordered_slot_completion
  let subs : Renamings := ({} : Renamings).insert ``Lax793645.FiniteScores.large_score_probability
      ``Lax793645Proofs.FiniteScores.large_score_probability
  let graph := ``Lax793645Proofs.Construction.arbitrarily_large_small_connected_matching
  let ((construction, ordinary), names) ← (do
    return (← rebuild graph, ← rebuild ``not_hadwiger_conjecture)).run subs
  let names := names
    |>.insert ``Lax793645.Counterexample.arbitrarily_large_small_connected_matching construction
    |>.insert ``Lax793645.MatchingMinorBound.hadwiger_matching_bound
      ``Lax793645Proofs.HadwigerMatching.hadwiger_matching_bound
    |>.insert ``Lax793645.FractionalColoring.fractional_chromatic_lower_bound
      ``Lax793645Proofs.FractionalColoring.fractional_chromatic_lower_bound
    |>.insert ``Lax793645.FractionalColoring.fractional_chromatic_le_chromatic
      ``Lax793645Proofs.FractionalColoring.fractional_chromatic_le_chromatic
  let (fractional, _) ← (rebuild
    ``Lax793645Proofs.FractionalCounterexample.arbitrarily_large_fractional_counterexample).run names
  for root in #[construction, ordinary, fractional] do
    let (_, used) ← (dependencies root).run {}
    for key in #[newGraph,newGram] do
      unless used.contains key do throwError "{root} does not use {key}"
    for key in #[oldGraph,oldGram,``patterned_block_rank_completion,
        ``exposure_tree_impossible,``tree_budget,``dyadic_exposure_joint] do
      if used.contains key then throwError "{root} still uses {key}"
    let axioms ← collectAxioms root
    unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "Unexpected axioms in {root}: {axioms}"
    logInfo m!"Checked {root} with the matching-list and ordered-slot proofs. Axioms: {axioms}"

end HadwigerVerification
