#!/usr/bin/env python3
"""Audit a freshly inspected, kernel-replayed standalone submission."""
import hashlib
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NS = "Lax793645"
TARGET = NS + ".Counterexample.arbitrarily_large_small_connected_matching"
FINITE = {
    NS + ".FiniteScores.large_score_probability",
}
SUPERSEDED = {
    NS + ".OverlapTransfer.clipped_transfer",
    NS + ".ResidualRegularity.common_partition",
    NS + ".AdaptivePartitions.common_partition",
}
# Archive descriptions are Lean module comments and can contain the English
# verb "admit". Only skip the initial documentation following plain imports.
ARCHIVE_DESCRIPTION = re.compile(
    r"\A((?:(?:import [\w.]+)?[ \t]*\n)*)/-!\n---\n.*?-/", re.DOTALL
)


def statement_dependencies(by_conclusion, roots):
    seen = set()
    pending = list(roots)
    while pending:
        statement = pending.pop()
        if statement in seen:
            continue
        seen.add(statement)
        for proof in by_conclusion[statement]:
            pending.extend(proof["assumptions"])
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", action="store_true",
                        help="Validate the original theorem while explicitly reporting pending replacements")
    args = parser.parse_args()
    output = ROOT / "build-output.json"
    assert output.is_file(), "Run lax build . --replay first"
    data = json.loads(output.read_text())
    assert data["id"] == "lax-793645"
    assert data.get("localValidation", {}).get("replay") is True, "Kernel replay missing"
    assert not data["requiredByConcepts"] and not data["requiredByProofs"], "Not standalone"
    statements = {s["id"] for c in data["concepts"] for s in c["statements"]}
    closed = set()
    while True:
        new = {p["conclusion"] for p in data["proofs"] if set(p["assumptions"]) <= closed}
        if new <= closed:
            break
        closed |= new
    assert statements <= closed, "Open statements: " + str(sorted(statements - closed))
    by_conclusion = {}
    for proof in data["proofs"]:
        assert set(proof["assumptions"]) <= closed
        by_conclusion.setdefault(proof["conclusion"], []).append(proof)
    for consequence in (
        NS + ".Counterexample.arbitrarily_large_hadwiger_counterexample",
        NS + ".FractionalCounterexample.arbitrarily_large_fractional_counterexample",
    ):
        assert all(TARGET in proof["assumptions"] for proof in by_conclusion[consequence]), \
            f"The graph construction is missing from {consequence}"
    ancestors = statement_dependencies(by_conclusion, [TARGET])
    assert FINITE <= ancestors, "Missing finite-score dependency"
    assert not (SUPERSEDED & ancestors), "Superseded overlap/regularity boundary still used"
    paper_proof_id = NS + "Proofs.Manuscript.Counterexample.arbitrarily_large_small_connected_matching"
    paper_proof, = (p for p in by_conclusion[TARGET] if p["id"] == paper_proof_id)
    paper_dependencies = statement_dependencies(by_conclusion, paper_proof["assumptions"])
    required_cards = {NS + "." + name for name in (
        "MatchingNeighborhoods.hitting_list", "MatchingExposure.transfer_scales",
        "OrderedSlotCompletion.ordered_slot_completion", "FourHoles.eventual_conflict_lower_bound",
        "SelectedAtoms.tensor_atom_isolation", "FrameRealization.one_reciprocal_realization",
        "FourierComparison.one_direct_capped_leaf_fourier", "FreshWitnessLists.seven_list",
        "PreparedUnits.one_finite_preparation", "PredictedScalarSystem.one_attained_scalar_soluble",
        "UnpredictedOverlap.one_quiet_end",
    )}
    assert required_cards <= paper_dependencies, sorted(required_cards - paper_dependencies)
    aggregate = NS + ".FiniteObstruction.threshold_bound"
    for proof in by_conclusion[aggregate]:
        assert set(proof["assumptions"]) == {
            NS + ".OverlapTransfer.finite_transfer",
            NS + ".FiniteScores.squared_score_probability",
        }
    inputs = [ROOT / f for f in ("manifest.yaml", "abstract.md", "LICENSE")]
    for package in ("concepts", "proofs"):
        inputs += [ROOT / package / f for f in ("lakefile.toml", "lean-toolchain")]
        inputs += list((ROOT / package).glob("*.lean"))
        module = NS + ("Proofs" if package == "proofs" else "")
        sources = list((ROOT / package / module).rglob("*.lean"))
        inputs += sources
        expected = {str(p.relative_to(ROOT / package)).removesuffix(".lean").replace("/", ".")
                    for p in sources}
        imports = [line.removeprefix("import ").strip()
                   for line in (ROOT / package / (module + ".lean")).read_text().splitlines()
                   if line.startswith("import ")]
        assert set(imports) == expected and len(imports) == len(expected), \
            f"Root module inventory is incomplete or duplicated: {package}"
    inputs += list((ROOT / "paper").rglob("*.tex")) + list((ROOT / "paper").rglob("*.bib"))
    assert all(p.stat().st_mtime_ns <= output.stat().st_mtime_ns for p in inputs), "Build output is stale"
    captured = {entry["path"]: entry["sha256"] for entry in data["capture"]["files"]}
    for p in inputs:
        rel = p.relative_to(ROOT)
        if rel.parts[0] in ("concepts", "proofs", "paper"):
            key = (rel if rel.parts[0] == "paper" else
                   Path(rel.parts[0], "package", *rel.parts[1:]))
            assert captured.get(key.as_posix()) == hashlib.sha256(p.read_bytes()).hexdigest(), \
                f"Source differs from the kernel replay capture: {rel}"
        if p.suffix == ".lean":
            code = p.read_text()
            assert "Lax342547" not in code, f"Old package reference: {p}"
            lean_body = ARCHIVE_DESCRIPTION.sub(r"\1", code, count=1)
            assert not re.search(r"\b(sorry|admit|native_decide)\b", lean_body), f"Unchecked code: {p}"
    original = json.loads((ROOT / "references/original-statement-audit.json").read_text())
    assert len(original["files"]) == 7
    for entry in original["files"]:
        current = (ROOT / entry["current_path"]).read_bytes()
        assert hashlib.sha256(current).hexdigest() == entry["current_sha256"], entry
        restored = current.decode().replace("Lax793645", "Lax342547").encode()
        assert hashlib.sha256(restored).hexdigest() == entry["original_sha256"], entry
    provenance = json.loads((ROOT / "references/finite-partition-port.json").read_text())
    for path, digest in provenance["source_sha256"].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
    audit = json.loads((ROOT / "references/further-simplifications-audit.json").read_text())
    new_sources = {str(p.relative_to(ROOT)) for p in
                   (ROOT / "proofs/Lax793645Proofs/Simplifications").glob("*.lean")}
    assert set(audit["source_sha256"]) == new_sources, "Incomplete simplification audit"
    for path, digest in audit["source_sha256"].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
    for name, axioms in audit["theorems"].items():
        assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, name
    integration = json.loads((ROOT / "references/further-integration-audit.json").read_text())
    assert integration["target"] == NS + "Proofs.Construction.arbitrarily_large_small_connected_matching"
    assert set(integration["integrated"]) == {"explicit_binary_matrices", "matching_neighborhoods", "ordered_slot_completion", "linear_query_partitions",
                                           "unified_predicted_overlap", "affine_selectors",
                                           "tester_coordinate_restrictions", "odd_cycle_geometry",
                                           "linear_common_projection", "linear_rare_overlap", "direct_query_tail_bounds", "linear_prediction_extraction", "linear_preparation", "linear_predictor_consistency", "quadratic_one_frame_construction", "reduced_mixer_family",
                                           "coordinate_quadratic_completion", "exact_support_scalar_extraction",
                                           "exact_algebraic_predictions", "seven_prediction_catalogue",
                                           "literal_prediction_classes", "pin_rank_consistency", "cell_sum_overlap",
                                           "direct_even_moments", "auxiliary_kernel_certificates",
                                           "full_linear_key_cells", "one_sided_projection_bound",
                                           "frame_rank_deficit_clipping", "automatic_label_span_stability", "support_surrogates",
                                           "generic_predictions_and_witnesses", "uniform_finite_preparation",
                                           "attained_predictor_cells", "reciprocal_ambient_rank",
                                           "conditional_compatibility_floor", "actual_cell_overlap",
                                           "generic_query_comparison", "constant_preparation_mass",
                                           "row_support_compatibility", "quadratic_frame_symmetry_by_counting",
                                           "finite_compatibility_labels", "four_zero_phase_bound", "complete_query_key_fibers",
                                           "direct_frequency_selection", "finite_subset_exposure"}
    assert {NS + "Proofs.Simplifications." + name for name in (
        "row_support_cut", "row_support_alternative", "row_support_probability", "mutual_zero_probability",
        "one_prescribed_one_span_alternative", "one_prescribed_one_outcome", "quadratic_column_exists",
        "OneDosed.crossing_of_span_bound", "OneDosed.offset_span_dispersion",
        "one_offset_list_mass", "one_offset_column_meets_primal",
        "quadratic_frame_symmetry", "quadratic_column_partner", "quadratic_column_signed_mass",
    )} <= set(integration["required_present"]), "Missing rank or frame replacement"
    assert {NS + "Proofs.Simplifications." + name for name in (
        "binary_clique_rank", "quadraticTransvection", "quadratic_one_vector",
    )} | {"QuadraticMap.le_radical_iff"} <= set(integration["forbidden_absent"]), "Old frame or clique proof present"
    assert {NS + "Proofs.Simplifications." + name for name in (
        "one_refine_compatibility", "one_floor_of_code", "one_four_zero_outcome", "four_zero_probability",
        "OneQuill.accepted_iff_feasible_key", "OneStation.full_key_overlap", "OneStation.filtered_match_le"
    )} <= set(integration["required_present"]), "Missing finite labels or full accepted key measures"
    assert {NS + "Proofs.Simplifications." + name for name in (
        "filtered_large_spectrum", "spectrum_all_filters", "subset_with_small_marginals",
        "shared_leaf_frequencies", "linear_uniform_common_overlap",
    )} <= set(integration["required_present"]), "Missing finite spectrum or subset argument"
    assert {NS + "Proofs.Simplifications." + name for name in (
        "all_filters_linear_partition", "one_query_density_refinement", "linear_test_refinement",
        "common_linear_intersections", "common_frequency_space", "rare_quotient_intersections",
    )} <= set(integration["forbidden_absent"]), "Old iterative selection still present"
    assert {NS + "Proofs.Simplifications." + name for name in (
        "MatchingNeighborhoods.hitting_list", "MatchingNeighborhoods.mixture_conflict",
        "MatchingNeighborhoods.matching_certificate_transfer", "ordered_slot_completion",
        "symmetric_low_rank_batch_weight",
    )} <= set(integration["required_present"]), "Missing matching-list or Gram completion proof"
    assert {NS + "Proofs.Simplifications." + name for name in (
        "matching_exposure_transfer", "dyadic_exposure_joint", "tree_budget",
        "symmetric_patterned_block_completion", "patterned_block_rank_completion",
    )} <= set(integration["forbidden_absent"]), "Superseded graph or Gram proof still present"
    pending = integration["not_yet_integrated"]
    if not args.checkpoint:
        assert pending == [], "Unfinished replacements: " + ", ".join(pending)
    required_absent = {
        "Lax793645Proofs.Upstream.OAI.HadwigerCounterexample." + name
        for name in ("Template.weakly", "Template.controls", "global_net", "erosive",
                     "silicon_calendar", "screen_calendar", "magazine_calendar", "rank_torpedo")
    }
    assert required_absent <= set(integration["forbidden_absent"]), "Incomplete analytic replacement audit"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "OneTypus.one_finite_support_calendar", "OneTypus.one_support_projected_mend",
        "projected_excess_test_bound", "one_fixed_rejected_common_projection"
    )} <= set(integration["required_present"]), "Missing support-based finite overlap proof"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "OneTypus.one_finite_score_calendar", "OneTypus.one_projected_surrogate_mend",
        "projected_density_mend", "OneQuill.one_linear_query_test"
    )} <= set(integration["forbidden_absent"]), "Probability-table comparison remains"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "coordinate_quadratic_extension", "one_exact_quadratic_population",
        "one_algebraic_cohort", "exact_seven_alternative",
        "one_attained_scalar_soluble", "one_exact_slopes_zero",
        "cycle_support_consistency", "OneQuill.one_base_product_relative_hit",
        "weighted_cell_lower", "clipped_overlap_comparison"
    )} <= set(integration["required_present"]), "Missing exact-prediction replacement"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "quadratic_frame_rows_cap", "one_tuple_rank_deficit", "one_linear_cell_cap_calendar",
        "one_unfiltered_bounded_approximation", "one_linear_query_controls",
        "dominated_approximation_tails"
    )} <= set(integration["required_present"]), "Missing frame-counting and clipping replacement"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "one_light_query_controls", "one_uniform_hit_calendar", "one_coordinate_hit_calendar"
    )} <= set(integration["forbidden_absent"]), "Repeated-hit route remains in the final proof"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "generic_status_band_stable", "one_generic_status_continuation_control", "one_status_input_converse",
        "one_predictor_label_extension", "one_generic_scalar_options"
    )} <= set(integration["required_present"]), "Missing polynomial span-continuation replacement"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "one_scalar_options", "independent_stable_supply", "stable_at_budget"
    )} <= set(integration["forbidden_absent"]), "Repeated span stabilization remains in the final proof"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "hyperbolic_relative_extension", "relative_quadratic_extension",
        "one_examine", "one_prune_whisper", "one_outlook_to_dose_preserving",
        "exists_majority_trace", "majority_trace_unique", "intrinsic_tester",
        "one_sparse_usual", "one_initial_leaf_calendar", "one_total_rank_shared",
        "cliff_thick_on", "cliff_score_on", "projected_superlevel_pr"
    )} <= set(integration["forbidden_absent"]), "Incomplete deletion audit"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "one_refute_finite_preparation", "one_finite_preparation", "one_preparation_cases",
        "one_cohort_calendar", "eventually_of_finite_cases", "one_predictor_cell_calendar",
        "one_exact_harmony", "attained_coordinate_mass", "one_finite_echoes",
        "one_zero_parity_mass", "one_direct_zero_certificate", "one_reciprocal_zero",
        "one_four_pattern_ambient", "one_singleton_bias_mass", "eventually_ambient_pattern_margin",
        "one_unrestricted_class", "finite_witness_with_floor", "actual_cell_overlap",
        "one_generic_identity_all", "one_generic_zero_all", "one_generic_seems_zero_iff"
    )} <= set(integration["required_present"]), "Missing finite preparation, scalar or overlap replacement"
    assert {NS + "Proofs.Simplifications." + name for name in (
        "one_prepare_cofinal", "finite_cofinal_choice", "restrict_frequent",
        "one_algebraic_dose_refine", "one_exact_cohorts_refine", "one_reference_separation_calendar",
        "one_finite_recital", "one_twinned_rank_compatibility", "one_circus_rank", "one_tiny_pattern_mass"
    )} <= set(integration["forbidden_absent"]), "Superseded assembly, separation or compatibility proof remains"
    duet = integration["local_two_position_query"]
    assert not duet["adopted_by_final_theorem"] and duet["target"] in integration["checked_but_not_adopted"]
    assert {NS + "Proofs.Simplifications." + name for name in (
        "one_status_coordinates_bounded", "oneChime", "two_position_accepted_mass"
    )} <= set(duet["required_present"]), "Missing actual two-position script or unary statuses"
    obstruction = integration["spreading_counterexample"]
    assert not obstruction["adopted_by_final_theorem"]
    assert obstruction["target"] == NS + "Proofs.Simplifications.one_spreading_zero_overlap"
    assert obstruction["target"] in integration["checked_but_not_adopted"]
    paired = integration["opposite_leaf_tests"]
    assert not paired["adopted_by_final_theorem"]
    assert paired["target"] == NS + "Proofs.Simplifications.OneVeil.opposite_leaf_tests"
    assert paired["target"] in integration["checked_but_not_adopted"]
    for key, name in (("own_leaf_character", "own_leaf_row_character"),
                      ("disjoint_key_sets", "quadratic_cut_linear_tests")):
        example = integration[key]
        assert example["target"] == NS + "Proofs.Simplifications." + name
        assert hashlib.sha256((ROOT / example["source"]).read_bytes()).hexdigest() == example["sha256"]
    assert {NS + "Proofs.Simplifications." + name for name in (
        "one_pooled_hit_product", "one_paired_fixed_test", "OneVeil.query_caps",
        "independent_leaf_tests"
    )} <= set(paired["required_present"]), "Incomplete mixed-law comparison"
    assert {NS + "Proofs.Simplifications." + name for name in (
        "one_image_pin_cap", "one_primal_pair_intersection_cap", "NoSharedOption.zero_overlap"
    )} <= set(obstruction["required_present"]), "Incomplete frame-law counterexample"
    assert "Filter.exists_ultrafilter_le" in integration["forbidden_absent"], "Ultrafilter choice remains"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "one_generic_lightmap", "one_generic_gauze_calendar", "OneStation.inform_generic_options",
        "fixed_mass_trim", "constant_mass_trim"
    )} <= set(integration["required_present"]), "Missing generic-query or fixed-mass preparation proof"
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "one_lightmap", "one_gauze_calendar", "one_silken"
    )} <= set(integration["forbidden_absent"]), "Shared analytic estimates remain"
    assert "Lax793645Proofs.Upstream.OAI.HadwigerCounterexample.vigor_trim" in integration["forbidden_absent"]

    local_core = integration["local_predictor_core"]
    assert local_core["adopted_by_final_theorem"] is False
    assert local_core["target"] in integration["checked_but_not_adopted"]
    assert {"Lax793645Proofs.Upstream.OAI.HadwigerCounterexample." + name
            for name in ("screen_calendar", "magazine_calendar", "rank_torpedo")} <= \
        set(local_core["forbidden_absent"]), "Incomplete local predictor dependency check"
    support_core = integration["local_exact_support_core"]
    assert support_core["adopted_by_final_theorem"] is False
    assert support_core["target"] in integration["checked_but_not_adopted"]
    assert {"Lax793645Proofs.Simplifications." + name for name in (
        "one_palette_support_space", "one_full_palette_status_gap",
        "one_table_gap_dual", "dual_exact_status_predictors", "exact_family_predictor"
    )} <= set(support_core["required_present"]), "Incomplete local support proof"
    assert {"Lax793645Proofs.Upstream.OAI.HadwigerCounterexample." + name for name in (
        "majority_charge", "StatusAnalysis.DualAnalysis.paeans",
        "StatusAnalysis.DualAnalysis.charge_counter"
    )} <= set(support_core["forbidden_absent"]), "Approximate extraction remains in local support proof"
    analytic = json.loads((ROOT / "references/linear-partitions-audit.json").read_text())
    for path, digest in analytic["source_sha256"].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
    quadratic = json.loads((ROOT / "references/quadratic-foundations-audit.json").read_text())
    for path, digest in quadratic["source_sha256"].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
    for path, digest in integration["source_sha256"].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
    paper = "\n".join(p.read_text() for p in (ROOT / "paper").rglob("*.tex"))
    labels = re.findall(r"\\label\{([^}]+)\}", paper)
    assert len(labels) == len(set(labels)), "Duplicate paper labels"
    refs = {item.strip() for group in re.findall(r"\\(?:Cref|cref|eqref|ref)\{([^}]+)\}", paper)
            for item in group.split(",")}
    assert refs <= set(labels), "Undefined paper references: " + str(sorted(refs - set(labels)))
    assert not re.search(r"\\(?:boxed|fbox)\b", paper), "Boxed mathematical result"
    assert (ROOT / "paper.pdf").is_file(), "No archive-compiled paper"
    print(f"CLOSED: all {len(statements)} statements, {len(data['proofs'])} annotated proofs, "
          f"{len(data['concepts'])} concepts")
    print("Both coloring counterexamples use the verified graph construction.")
    print(f"The marked graph proof reaches {len(paper_dependencies)} other archive statements.")
    print("Construction uses the direct projected-density estimate and finite score suppression; the archived clipped-transfer and regularity boundaries are independent auxiliary statements.")
    print("Standalone dependencies, replay, source hashes, and paper references verified.")
    print(f"Additionally audited {len(audit['theorems'])} simplification theorems.")
    print("The graph proof uses every attained predictor pair, one uniform finite preparation quota, and the direct ambient rank bound for the two reciprocal zero parities.")
    print("A separate Lean theorem exhibits one spreading frame law with zero overlap for all complete options.")
    if pending:
        print("CHECKPOINT ONLY. The original theorem is verified; the requested simplification program is unfinished.")
        print("Pending: " + ", ".join(pending))


if __name__ == "__main__":
    main()
