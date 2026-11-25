#!/usr/bin/env python3
"""Audit the new realization theorem, without claiming final construction adoption."""
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "proofs"
UP = "Lax793645Proofs.Upstream.OAI.HadwigerCounterexample."
NEW = "Lax793645Proofs.Simplifications."
COMMON_FORBIDDEN = [UP + name for name in (
    "gradient_realization", "Volley.realize_linear", "Volley.split_orth",
    "Volley.clean_effective", "label_support", "flat_atLayer", "flat_entries",
    "shift_factors", "selector_indep", "pin_protection",
)]
AUDITS = [
    ("AffineGradientRealization", "affine_gradient_realization", [NEW + name for name in (
        "selector_confinement", "tensor_atom_isolation", "protected_tensor_annihilator",
        "affine_component_isolation", "linear_star_constant", "affine_split_orth",
        "RaySeparation.residual_effective", "affine_realize_linear", "affine_key_independent",
    )], COMMON_FORBIDDEN),
    ("AffinePairedCollisionBounds", "AffineOptions.arena_bound", [NEW + name for name in (
        "affine_gradient_realization", "affine_collision", "affine_key_slots",
        "collision_on_accepted_slots", "record_hit_of_slots",
    )], COMMON_FORBIDDEN + [UP + name for name in (
        "Volley.collision", "Volley.record_hit", "StatusAnalysis.Station.sellPoint",
    )]),
    ("AffineScalarOptions", "affine_scalar_options", [NEW + name for name in (
        "affine_processions", "independent_invite", "independent_stable_supply",
        "independent_full_parade", "IndependentClub.seven_of_deletion_stability",
        "plenitude_at_budget", "plan_protection_exists", "affine_optionVia",
    )], COMMON_FORBIDDEN + [UP + name for name in (
        "StatusAnalysis.DualAnalysis.processions", "StatusAnalysis.DualAnalysis.invite",
        "StatusAnalysis.Guild.full_parade", "StatusAnalysis.optionVia",
        "StatusAnalysis.shelter", "StatusAnalysis.buildBooths",
    )]),
    ("FiniteRejectionTransfer", "density_mend_after_rejection", [NEW + name for name in (
        "density_mend_clipped", "good_input_truncated_overlap",
    )], []),
    ("AffineParameterExistence", "AffineParameters.exists_affine_parameters", [NEW + name for name in (
        "AffineParameters.seed_affine_ribbon", "AffineRealizeAssum",
    )], COMMON_FORBIDDEN + [UP + "exists_parameters"]),
    ("AffinePredictedOptions", "affine_predicted_options_of_plan", [NEW + name for name in (
        "affine_predicted_labels", "independent_selector_choice", "affine_optionVia",
    )], COMMON_FORBIDDEN),
    ("AffinePredictedPairedBounds", "AffineOptions.predicted_dimBerth", [NEW + name for name in (
        "AffineOptions.ownCertificate", "AffineOptions.predicted_qualify_hit",
        "affine_sales_rejection", "AffineVeil.score_cost",
    )], COMMON_FORBIDDEN),
    ("AffineKeyProjection", "AffineOptions.projectCut", [NEW + name for name in (
        "density_mend_after_rejection", "affine_sales_rejection_of_filter", "AffineVeil.score_cost",
    )], COMMON_FORBIDDEN),
    ("AffineQueryLoss", "affine_sales_rejection", [NEW + name for name in (
        "hist_rejection", "affine_query_rejection", "template_base_rejection",
    )], COMMON_FORBIDDEN),
]


def run(args):
    result = subprocess.run(args, cwd=PROOFS, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(["lake", "build", *(NEW + module for module, *_ in AUDITS)])
    prelude = "\n".join("import " + NEW + module for module, *_ in AUDITS)
    prelude += '''
import Lean
open Lean Elab Command
partial def visitAffineDependencies (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  if let some info := env.find? name then
    info.type.getUsedConstants.forM (visitAffineDependencies env)
    if let some value := info.value? (allowOpaque := true) then
      value.getUsedConstants.forM (visitAffineDependencies env)
    if let .inductInfo data := info then
      data.ctors.forM (visitAffineDependencies env)
'''
    blocks = []
    for _, target, required, forbidden in AUDITS:
        blocks.append('''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let seen := (visitAffineDependencies env `TARGET).run {} |>.2
  for name in NAMES do
    unless env.contains name do throwError m!"Unknown audit target: {name}"
    logInfo m!"DEPENDENCY TARGET -> {name}: {seen.contains name}"
#print axioms TARGET
'''.replace("TARGET", NEW + target).replace(
            "NAMES", "[" + ", ".join("`" + n for n in required + forbidden) + "]"))
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as file:
        file.write(prelude + "\n".join(blocks))
        path = Path(file.name)
    try:
        output = run(["lake", "env", "lean", str(path)])
    finally:
        path.unlink()
    for _, target, required, forbidden in AUDITS:
        for name in required:
            assert f"DEPENDENCY {NEW + target} -> {name}: true" in output, output
        for name in forbidden:
            assert f"DEPENDENCY {NEW + target} -> {name}: false" in output, output
    paths = sorted((PROOFS / "Lax793645Proofs/Simplifications").glob("*.lean"))
    report = {
        "scope": "Affine algebra, parameter existence, option production and both analytic branches; "
                 "final adoption is independently checked by check_integration.py",
        "audits": [{"target": NEW + target, "required_present": required,
                    "forbidden_absent": forbidden}
                   for _, target, required, forbidden in AUDITS],
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in paths},
        "output": output,
    }
    (ROOT / "references/affine-realization-audit.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(output, end="")
    print(f"CHECKED: {len(AUDITS)} affine proof boundaries use the new proofs.")
    print("Run check_integration.py for final counterexample adoption.")


if __name__ == "__main__":
    main()
