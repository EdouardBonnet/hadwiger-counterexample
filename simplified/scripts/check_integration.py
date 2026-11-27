#!/usr/bin/env python3
"""Check actual proof-term adoption, independently of imported module names."""
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / "proofs"
UP = "Lax793645Proofs.Upstream.OAI.HadwigerCounterexample."
NEW = "Lax793645Proofs.Simplifications."
TARGET = "Lax793645Proofs.Construction.arbitrarily_large_small_connected_matching"
REQUIRED = [UP + "exists_graphs"] + [NEW + name for name in (
    "explicitReduced_binary_rank", "explicitReduced_unary",
    "goodReducedMixers", "reduced_polar_likely", "reducedUrBad_cap",
    "reduced_stack_surj", "reduced_mass_positive", "choose_reduced_script",
    "cycle_weight_star", "reduced_reads_iff", "reduced_mixer_law",
    "MatchingNeighborhoods.hitting_list", "MatchingNeighborhoods.mixture_conflict",
    "MatchingNeighborhoods.matching_certificate_transfer",
    "ordered_slot_completion", "symmetric_low_rank_batch_weight",
    "OneConstruction.exists_graphs", "OneParameters.exists_parameters",
    "one_refute_veil", "one_quiet_end", "one_refute_finite_preparation", "one_finite_preparation",
    "one_preparation_cases", "one_cohort_calendar", "eventually_of_finite_cases", "one_predicted_certificate",
    "one_direct_zero_certificate", "one_zero_parity_mass", "one_reciprocal_zero",
    "one_twinned_ambient_mass", "one_singleton_ambient_mass", "one_unrestricted_class",
    "finite_witness_with_floor", "one_floor_of_code", "actual_cell_overlap",
    "PairCode.named_both", "one_offset_span_code", "one_coded_of_span", "one_spanned_of_cover",
    "one_refine_labels", "one_refine_leaf_labels", "one_refine_compatibility",
    "OneDurable.coded_safety", "OneDurable.coded_rare_pairs",
    "one_diag_dusk_endpoint", "four_zero_probability", "one_four_zero_span", "one_four_zero_outcome",
    "OneStation.filtered_match_le", "OneStation.full_key_overlap", "overlap_of_mixtures",
    "OneQuill.good_histogram_eq_feasible", "OneQuill.accepted_iff_feasible_key", "OneQuill.draw_eq_of_keys_eq",
    "OneOptions.predicted_gold_end", "OneOptions.predicted_dim_end",
    "OneOptions.predicted_mass_bounds", "OneStation.one_predicted_dim_berth",
    "one_attained_scalar_soluble", "one_exact_harmony", "one_finite_echoes",
    "one_predictor_cell_calendar", "one_attained_cell_calendar", "attained_coordinate_mass", "predicted_three_list",
    "one_predicted_options_of_plan", "one_predicted_labels",
    "OneQuill.one_predicted_query_error", "OneQuill.one_protected_predicted_hit",
    "one_hole_triangle", "one_raw_law", "one_frame_primal_observe",
    "one_scalar_realization", "coordinate_quadratic_extension", "coordinate_quadratic_baseline",
    "coordinate_quadratic_correction", "relative_quadratic_baseline", "selector_confinement", "tensor_atom_isolation",
    "one_phase_alternative", "one_first_leaves",
    "row_support_cut", "row_support_alternative", "row_support_probability",
    "one_prescribed_one_span_alternative", "one_prescribed_one_outcome",
    "OneDosed.crossing_of_span_bound", "OneDosed.offset_span_dispersion",
    "one_offset_list_mass", "one_offset_column_meets_primal",
    "zero_entry_probability", "mutual_zero_probability",
    "one_four_pattern_ambient", "eventually_ambient_pattern_margin", "one_singleton_bias_mass",
    "quadratic_column_signed_mass", "quadratic_column_mass", "quadratic_column_partner",
    "quadratic_frame_symmetry", "quadratic_gauss_abs", "quadratic_column_exists",
    "quadratic_point_symmetry",
    "one_direct_moment_decay", "one_direct_capped_leaf_fourier", "one_auxiliary_query_moment",
    "one_auxiliary_frame_bound", "auxiliary_normalized_batch_bound", "auxiliary_network_expansion",
    "auxiliary_network_expansion_cost", "auxiliary_network_kernel", "auxiliary_kernel_certificate",
    "auxiliary_batch_fourier", "auxiliary_even_budget_calendar",
    "one_capped_leaf_comparison", "one_query_all_filters_linear_partition",
    "filtered_large_spectrum", "spectrum_all_filters", "one_query_linear_energy_calendar",
    "subset_with_small_marginals",
    "one_capped_input_status_comparison", "one_successful_query_linear_partition",
    "one_rejected_successful_common_projection", "one_fixed_rejected_common_projection",
    "OneTypus.one_finite_support_calendar", "OneTypus.one_support_projected_mend",
    "OneTypus.one_average_support_score_bound", "OneTypus.one_filtered_support_shine",
    "OneQuill.one_support_linear_comparison_calendar", "OneQuill.one_support_linear_query_domination",
    "OneQuill.one_support_cell_domination", "OneQuill.one_support_projected_error",
    "OneQuill.one_average_support_error", "one_reflected_status_atom_bound",
    "affine_fiber_status_gap", "stained_linear_status_gap", "projected_excess_test_bound",
    "one_engagement_support", "one_chart_status_bound", "one_sided_projected_mend", "one_generic_lightmap", "OneExactOptions.no_out",
    "OneVeil.exact_catalog_calendar", "one_exact_catalog_control", "one_palette_good_mass",
    "one_exact_span_catalog_control", "one_generic_status_continuation_control",
    "one_status_input_converse", "one_reference_color_empirical",
    "generic_status_band_stable", "generic_status_predictors", "signal_rhyme_form", "whole_rhyme_form",
    "one_predictor_label_extension", "one_generic_scalar_options", "generic_independent_invite",
    "one_generic_silken", "one_generic_gauze_calendar", "OneAppearance.oneGenericDemonstrates",
    "one_generic_plume_reports", "OneQuill.one_generic_gauze_area",
    "OneStation.generic_score_calendar", "OneStation.generic_simultaneous_calendar",
    "OneStation.generic_prognosis", "one_generic_late_scores", "one_generic_sick_bound",
    "one_generic_route_live", "OneStation.inform_generic_options",
    "fixed_mass_trim", "constant_mass_trim",
    "one_generic_identity_all", "one_generic_seems_zero_iff", "one_generic_zero_all",
    "one_exact_endpoint_prediction", "one_exact_status_input", "one_exact_yoke_inputs",
    "exact_seven_alternative", "exact_edge_catalog", "exact_prediction_catalog",
    "seven_prediction_pairs_card", "exact_status_uniqueness", "exact_zero_bit_prediction",
    "one_table_support_gap", "one_full_palette_status_gap", "one_palette_support_space",
    "conditional_status_overlap_gap", "support_rectangle_constant", "dual_exact_status_predictors",
    "one_full_linear_key_palette", "one_full_linear_bundle", "one_full_linear_duo",
    "shared_leaf_frequencies", "linear_uniform_common_overlap", "one_successful_product_partition",
    "OneQuill.one_base_product_comparison_calendar", "OneQuill.one_base_product_hit_gain",
    "OneQuill.one_base_cell_query_comparison", "OneQuill.one_base_paint_query_comparison",
    "one_light_certificate", "one_linear_query_controls", "one_unfiltered_bounded_approximation",
    "dominated_approximation_tails", "one_linear_cell_cap_calendar", "one_tuple_deficit_calendar",
    "one_tuple_rank_deficit", "one_tuple_rows_zero_cap", "one_independent_rows",
    "hyperbolic_frame_rows_cap", "quadratic_frame_rows_cap", "quadratic_rows_orbit",
    "linear_slot_large_rank", "linear_rank_restriction", "one_uniform_query_cell",
    "uniform_free_cell_cap", "linear_affine_cell_cap", "linear_cell_reference_comparison",
    "one_prepared_linear_rank",
    "one_exact_quadratic_population", "one_common_quadratic_exact", "exact_quadratic_predictor",
    "one_quadratic_population_of_forms", "one_yoke_section_coordinates",
    "one_algebraic_cohort",
    "one_exact_slopes_zero", "one_exact_tester_support", "one_exact_cell_tester_rank",
    "one_phase_absent_exact", "cycle_support_consistency", "ordinaryBit_support",
    "quadratic_switch_constant_slope",
    "OneQuill.one_base_product_relative_hit", "weighted_cell_lower", "clipped_overlap_comparison",
    "CycleGeometry.cut_star_constant",
    "CycleTesterRouting.role_at", "CycleTesterRouting.shared_at",
)]
FORBIDDEN = [UP + name for name in (
    "StatusAnalysis.DualAnalysis.build_anthology", "StatusAnalysis.DualAnalysis.quotes",
    "StatusAnalysis.DualAnalysis.tells", "StatusAnalysis.DualAnalysis.paeans",
    "StatusAnalysis.DualAnalysis.charge_counter", "majority_charge",
    "simultaneous_czeros", "eventually_tiny_poll",
    "containers", "terminal", "legacy_binary_likely", "path_energy", "tax_antitone", "price",
    "goodMixers", "polar_likely", "urBad_cap",
    "Template.weakly", "Template.controls", "Template.legacy_controls",
    "Template.hist_calendar", "var_tension", "ample_thresh", "coFiber", "fiber_growth",
    "StatusAnalysis.legacy_goldEnd", "StatusAnalysis.legacy_dim_end",
    "StatusAnalysis.foretold", "StatusAnalysis.laysScore",
    "gradient_realization", "Volley.realize_linear", "Volley.split_orth",
    "Volley.clean_effective", "label_support", "flat_atLayer", "flat_entries",
    "shift_factors", "selector_indep", "pin_protection", "exists_parameters",
    "vigor_trim", "sparse_usual", "Wtag_majority_star", "totalRank_shared", "global_net",
    "global_net_implementation", "erosive", "erosive_implementation",
    "silicon_calendar", "screen_calendar", "magazine_calendar", "rank_torpedo",
    "havoc_rate", "mute_rate", "PreparationParameters.prepare",
)] + [NEW + name for name in (
    "matching_exposure_transfer", "exposure_tree_impossible", "retained_exposure_joint",
    "dyadic_exposure_joint", "bayes_average", "tree_budget",
    "symmetric_patterned_block_completion", "patterned_block_rank_completion",
    "one_quadratic_population", "one_common_quadratic_fit", "quadratic_switch_exact",
    "polynomial_agreement_exact", "OneOptions.no_out",
    "one_query_high_moment", "one_query_moment_decay", "one_capped_leaf_fourier",
    "quadratic_dependent_batch_bound", "quadratic_network_sieve_fourier_norm",
    "quadratic_corner_batch_fourier", "four_corner_max_rank",
    "AffineConstruction.exists_graphs", "affine_gradient_realization",
    "explicitMixer_binary_rank", "explicitMixer_unary",
    "query_high_moment", "clipped_successful_common_projection",
    "quadratic_ample_thresh", "colored_quadratic_bound", "slice_variance_from_query",
    "hyperbolic_relative_extension", "relative_quadratic_extension",
    "binary_clique_rank", "zero_pair_probability", "alternating_zero_probability",
    "quadratic_frame_move", "quadratic_move_fixing", "quadratic_move_pair", "quadraticTransvection",
    "quadratic_one_vector", "quadratic_plane_value", "quadratic_frozen_embedding",
    "one_examine", "one_prune_whisper", "one_outlook_to_dose_preserving",
    "one_linear_screen_slopes", "one_linear_silicon_calendar", "one_phase_absent_linear",
    "one_recenter_query_uniform",
    "exists_majority_trace", "majority_trace_unique", "intrinsic_tester", "sharedBit_support",
    "one_sparse_usual", "one_initial_leaf_calendar", "one_total_rank_shared",
    "cliff_thick_on", "cliff_score_on", "projected_superlevel_pr",
    "all_filters_linear_partition", "filtered_density_progress", "filtered_density_gain",
    "one_query_density_refinement", "linear_supported_refinement", "linear_test_refinement",
    "linear_test_partition", "common_linear_intersections", "common_frequency_space",
    "rare_quotient_intersections",
    "one_light_query_controls", "one_query_setwise_from_tails",
    "one_uniform_hit_calendar", "one_coordinate_hit_calendar", "one_actual_hit_tail",
    "one_lightmap", "one_late_scores", "OneStation.score_calendar",
    "OneStation.simultaneous_calendar", "one_gauze_calendar", "one_silken",
    "one_plume_reports", "one_route_live", "OneStation.inform_options",
    "one_scalar_options", "independent_stable_supply", "stable_at_budget",
    "OneTypus.one_finite_score_calendar", "OneTypus.one_projected_surrogate_mend",
    "projected_density_mend", "OneTypus.one_average_score_bound",
    "OneQuill.one_average_projected_error", "OneQuill.one_linear_comparison_calendar",
    "OneQuill.one_linear_query_test", "OneQuill.one_cell_query_comparison",
    "OneQuill.one_cell_surrogate_close", "OneQuill.one_base_prowl_ink",
    "OneQuill.one_base_sheen_ink",
    "one_prepare_linear", "one_algebraic_prediction_dose", "one_exact_cohorts_to_dose",
    "one_prepare_cofinal", "finite_cofinal_choice", "restrict_frequent",
    "one_algebraic_dose_refine", "one_exact_cohorts_refine", "one_finite_recital",
    "one_reference_separation_calendar", "bounded_coordinate_separation",
    "one_twinned_rank_compatibility", "finite_witness_rare",
    "oneStory", "one_story_ok", "one_story_size", "oneSpecialLeaf", "one_phase_fixed",
    "one_tiny_pattern_mass", "eventually_mutual_zero_margin", "one_circus_rank", "one_tiny_morn",
    "status_band_stable", "one_status_continuation_control", "one_scalar_options_stable",
)] + ["Filter.exists_ultrafilter_le", "QuadraticMap.le_radical_iff"]
PENDING = [NEW + name for name in (
    "quadratic_cell_predictor_gap", "one_conditional_status_gap",
    "one_exact_dual_predictions", "one_two_position_full_status_mass", "one_duet_status_request", "two_position_filtered_overlap",
    "opposite_binary_queries", "reciprocal_zero_diagonal_example",
    "one_common_key_primal_intersection", "one_opposite_frame_slices", "one_capped_opposite_keys",
    "one_capped_opposite_keys_calendar", "NoSharedOption.zero_overlap", "one_spreading_zero_overlap",
    "OneStation.full_key_cuts_of_collision", "OneVeil.opposite_leaf_tests")]
PENDING_MODULES = ["LinearCellPredictors"]
LOCAL_PREDICTOR_REQUIRED = [NEW + name for name in (
    "tester_affine_disagreement", "cell_slope_error", "odd_cell_parity")]
LOCAL_PREDICTOR_FORBIDDEN = [UP + name for name in (
    "screen_calendar", "magazine_calendar", "rank_torpedo")]
SUPPORT_REQUIRED = [NEW + name for name in (
    "one_full_palette_coordinates", "full_linear_coordinates", "one_full_cell_reference",
    "one_palette_input_cells", "one_status_coordinates_bounded", "one_full_palette_status_gap",
    "one_table_support_gap", "full_cell_status_overlap_gap", "affine_scoped_overlap_gap",
    "conditional_status_overlap_gap", "one_palette_support_space", "one_table_gap_dual",
    "dual_supported_eq", "dual_cell_support_eq", "exact_family_predictor",
    "support_rectangle_constant", "dual_exact_status_predictors")]
SUPPORT_FORBIDDEN = [UP + name for name in (
    "majority", "majority_bound", "majority_charge",
    "StatusAnalysis.DualAnalysis.paeans", "StatusAnalysis.DualAnalysis.charge_counter")] + [NEW + name for name in (
    "one_common_quadratic_fit", "quadratic_cell_predictor_gap", "quadratic_switch_exact")]
DUET_REQUIRED = [NEW + name for name in (
    "oneChime", "oneCallOne", "one_status_coordinates_bounded", "two_position_accepted_mass",
    "affine_key_slice_mass", "TwoPositionQuery.status_witness_mass")]
DUET_FORBIDDEN = [NEW + name for name in (
    "one_direct_moment_decay", "one_linear_query_controls", "one_phase_alternative")]
OBSTRUCTION_REQUIRED = [NEW + name for name in (
    "one_capped_opposite_keys_calendar", "one_image_pin_cap", "one_primal_pair_intersection_cap",
    "NoSharedOption.zero_overlap")]
PAIRED_REQUIRED = [NEW + name for name in (
    "one_pooled_hit_product", "one_query_small_set", "one_variance_calendar",
    "one_paired_fixed_test", "independent_leaf_tests", "OneVeil.query_caps")] + [UP + "paired_spread"]


def run(args):
    result = subprocess.run(args, cwd=PROOFS, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    run(["lake", "build", "Lax793645Proofs", "Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.Main",
         "Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RandomBinaryMixing",
         *("Lax793645Proofs.Simplifications." + m for m in PENDING_MODULES)])
    code = '''import Lax793645Proofs
PENDING_IMPORTS
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.Main
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.RandomBinaryMixing
import Lean
open Lean Elab Command
partial def visitDependencies (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  if let some info := env.find? name then
    info.type.getUsedConstants.forM (visitDependencies env)
    if let some value := info.value? (allowOpaque := true) then
      value.getUsedConstants.forM (visitDependencies env)
    if let .inductInfo data := info then
      data.ctors.forM (visitDependencies env)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let reached := (visitDependencies env `TARGET).run {} |>.2
  -- Private declarations carry generated prefixes. Audit their user names
  -- while traversing the original proof constants above.
  let known := env.constants.fold (init := ({} : NameSet))
    (fun names name _ => names.insert (privateToUserName name))
  let mut seen : NameSet := {}
  for name in reached do
    seen := seen.insert (privateToUserName name)
  for name in REQUIRED do
    unless known.contains name do throwError m!"Unknown required audit target: {name}"
  for name in NAMES do
    logInfo m!"DEPENDENCY {name}: {seen.contains name}"
  let localSeen := (visitDependencies env `LOCAL_TARGET).run {} |>.2
  for name in LOCAL_NAMES do
    unless env.contains name do throwError m!"Unknown local predictor audit target: {name}"
    logInfo m!"LOCAL_PREDICTOR {name}: {localSeen.contains name}"
  let supportSeen := (visitDependencies env `SUPPORT_TARGET).run {} |>.2
  for name in SUPPORT_LIST do
    unless env.contains name do throwError m!"Unknown support audit target: {name}"
    logInfo m!"EXACT_SUPPORT {name}: {supportSeen.contains name}"
  let duetSeen := (visitDependencies env `DUET_TARGET).run {} |>.2
  for name in DUET_LIST do
    unless env.contains name do throwError m!"Unknown duet audit target: {name}"
    logInfo m!"ACTUAL_DUET {name}: {duetSeen.contains name}"
  let obstruction := (visitDependencies env `OBSTRUCTION_TARGET).run {} |>.2
  for name in OBSTRUCTION_LIST do
    unless env.contains name do throwError m!"Unknown frame obstruction audit target: {name}"
    logInfo m!"ZERO_OVERLAP {name}: {obstruction.contains name}"
  let paired := (visitDependencies env `PAIRED_TARGET).run {} |>.2
  for name in PAIRED_LIST do
    unless env.contains name do throwError m!"Unknown paired query audit target: {name}"
    logInfo m!"PAIRED_QUERY {name}: {paired.contains name}"
'''.replace("PENDING_IMPORTS", "\n".join("import Lax793645Proofs.Simplifications." + m for m in PENDING_MODULES)).replace("`TARGET", "`" + TARGET).replace("REQUIRED",
        "[" + ", ".join("`" + n for n in REQUIRED + FORBIDDEN + PENDING) + "]").replace(
        "LOCAL_NAMES", "[" + ", ".join("`" + n for n in LOCAL_PREDICTOR_REQUIRED + LOCAL_PREDICTOR_FORBIDDEN) + "]").replace(
        "LOCAL_TARGET", NEW + "quadratic_cell_predictor_gap").replace(
        "SUPPORT_TARGET", NEW + "one_exact_dual_predictions").replace(
        "DUET_TARGET", NEW + "one_two_position_full_status_mass").replace(
        "DUET_LIST", "[" + ", ".join("`" + n for n in DUET_REQUIRED + DUET_FORBIDDEN) + "]").replace(
        "OBSTRUCTION_TARGET", NEW + "one_spreading_zero_overlap").replace(
        "OBSTRUCTION_LIST", "[" + ", ".join("`" + n for n in OBSTRUCTION_REQUIRED + DUET_FORBIDDEN) + "]").replace(
        "PAIRED_TARGET", NEW + "OneVeil.opposite_leaf_tests").replace(
        "PAIRED_LIST", "[" + ", ".join("`" + n for n in PAIRED_REQUIRED + DUET_FORBIDDEN) + "]").replace(
        "SUPPORT_LIST", "[" + ", ".join("`" + n for n in SUPPORT_REQUIRED + SUPPORT_FORBIDDEN) + "]").replace(
        "NAMES", "[" + ", ".join("`" + n for n in REQUIRED + FORBIDDEN + PENDING) + "]")
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", delete=False) as f:
        f.write(code)
        path = Path(f.name)
    try:
        output = run(["lake", "env", "lean", str(path)])
    finally:
        path.unlink()
    for name in REQUIRED:
        assert f"DEPENDENCY {name}: true" in output, output
    for name in FORBIDDEN + PENDING:
        assert f"DEPENDENCY {name}: false" in output, output
    for name in LOCAL_PREDICTOR_REQUIRED:
        assert f"LOCAL_PREDICTOR {name}: true" in output, output
    for name in LOCAL_PREDICTOR_FORBIDDEN:
        assert f"LOCAL_PREDICTOR {name}: false" in output, output
    for name in SUPPORT_REQUIRED:
        assert f"EXACT_SUPPORT {name}: true" in output, output
    for name in SUPPORT_FORBIDDEN:
        assert f"EXACT_SUPPORT {name}: false" in output, output
    for name in DUET_REQUIRED:
        assert f"ACTUAL_DUET {name}: true" in output, name
    for name in DUET_FORBIDDEN:
        assert f"ACTUAL_DUET {name}: false" in output, name
    for name in OBSTRUCTION_REQUIRED:
        assert f"ZERO_OVERLAP {name}: true" in output, name
    for name in DUET_FORBIDDEN:
        assert f"ZERO_OVERLAP {name}: false" in output, name
    for name in PAIRED_REQUIRED:
        assert f"PAIRED_QUERY {name}: true" in output, name
    for name in DUET_FORBIDDEN:
        assert f"PAIRED_QUERY {name}: false" in output, name
    def check_example(filename, theorem):
        path = ROOT / "verification" / filename
        name = NEW + theorem
        result = run(["lake", "env", "lean", str(path)])
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", result)
        assert match, result
        axioms = [a.strip() for a in match[1].split(",")]
        assert set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}, result
        return {"target": name, "source": str(path.relative_to(ROOT)),
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "axioms": axioms}

    own_row = check_example("own-leaf-row.lean", "own_leaf_row_character")
    disjoint = check_example("linear-tests-and-overlap.lean", "quadratic_cut_linear_tests")
    paths = list((PROOFS / "Lax793645Proofs").rglob("*.lean"))
    report = {
        "target": TARGET,
        "required_present": REQUIRED,
        "forbidden_absent": FORBIDDEN,
        "integrated": ["explicit_binary_matrices", "matching_neighborhoods", "ordered_slot_completion", "linear_query_partitions",
                       "unified_predicted_overlap", "affine_selectors", "tester_coordinate_restrictions",
                       "odd_cycle_geometry", "linear_common_projection", "linear_rare_overlap", "direct_query_tail_bounds", "linear_prediction_extraction", "linear_preparation", "linear_predictor_consistency", "quadratic_one_frame_construction", "reduced_mixer_family",
                       "coordinate_quadratic_completion", "exact_support_scalar_extraction",
                       "exact_algebraic_predictions", "seven_prediction_catalogue",
                       "literal_prediction_classes", "pin_rank_consistency", "cell_sum_overlap", "direct_even_moments", "auxiliary_kernel_certificates",
                       "full_linear_key_cells", "one_sided_projection_bound", "frame_rank_deficit_clipping",
                       "automatic_label_span_stability", "support_surrogates",
                       "generic_predictions_and_witnesses", "uniform_finite_preparation",
                       "attained_predictor_cells", "reciprocal_ambient_rank",
                       "conditional_compatibility_floor", "actual_cell_overlap",
                       "generic_query_comparison", "constant_preparation_mass",
                       "row_support_compatibility", "quadratic_frame_symmetry_by_counting",
                       "finite_compatibility_labels", "four_zero_phase_bound", "complete_query_key_fibers",
                       "direct_frequency_selection", "finite_subset_exposure"],
        "not_yet_integrated": ["generic_only_query_family", "cover_free_preparation_in_all_cases",
                               "partition_free_overlap_for_all_query_templates"],
        "superseded_integrations": ["slice_from_unary_variance", "majority_trace_consistency",
                                    "true_intersection_truncation", "relative_quadratic_extension",
                                    "limiting_prediction_classes", "superlevel_overlap",
                                    "four_corner_query_moments", "image_kernel_sieve",
                                    "fixed_accuracy_quadratic_fitting", "approximate_prediction_dictionary",
                                    "repeated_hit_clipping", "repeated_label_span_stabilization",
                                    "ultrafilter_selection", "shared_input_prediction_requirement",
                                    "cofinal_branch_selection", "prediction_class_separation_tolerance"],
        "remaining_formal_conventions": ["eventual_bounds_for_asymptotic_estimates"],
        "checked_but_not_adopted": PENDING,
        "spreading_counterexample": {
            "target": NEW + "one_spreading_zero_overlap",
            "required_present": OBSTRUCTION_REQUIRED,
            "forbidden_absent": DUET_FORBIDDEN,
            "adopted_by_final_theorem": False,
        },
        "opposite_leaf_tests": {
            "target": NEW + "OneVeil.opposite_leaf_tests",
            "required_present": PAIRED_REQUIRED,
            "forbidden_absent": DUET_FORBIDDEN,
            "adopted_by_final_theorem": False,
        },
        "own_leaf_character": own_row,
        "disjoint_key_sets": disjoint,
        "local_two_position_query": {
            "target": NEW + "one_two_position_full_status_mass",
            "required_present": DUET_REQUIRED,
            "forbidden_absent": DUET_FORBIDDEN,
            "adopted_by_final_theorem": False,
        },
        "local_predictor_core": {
            "target": NEW + "quadratic_cell_predictor_gap",
            "required_present": LOCAL_PREDICTOR_REQUIRED,
            "forbidden_absent": LOCAL_PREDICTOR_FORBIDDEN,
            "adopted_by_final_theorem": False,
        },
        "local_exact_support_core": {
            "target": NEW + "one_exact_dual_predictions",
            "required_present": SUPPORT_REQUIRED,
            "forbidden_absent": SUPPORT_FORBIDDEN,
            "adopted_by_final_theorem": False,
        },
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(paths)},
    }
    (ROOT / "references/further-integration-audit.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(output, end="")
    print(f"CHECKED: {len(REQUIRED)} required dependencies occur; {len(FORBIDDEN)} replaced dependencies are absent.")
    print("Ambient row supports give inverse-square reciprocal zero mass and inverse-fourth-power four-bit mass with the singleton character estimate.")
    print("The local exact-support extraction uses the actual palette and status laws; majority extraction and approximate fitting are absent from its proof.")
    print("The final theorem uses direct even moments and auxiliary kernel certificates; the four-corner moment route and image-kernel sieve are absent.")
    print("The final theorem uses exact status supports, seven canonical predictor pairs and exact algebraic prediction preparation. Approximate extraction and fixed-accuracy fitting are absent.")
    print("The partition and clipping bounds use frame row counts and bounded approximation; repeated-hit bounds are absent from the final proof.")
    print("Polynomial continuation preserves every edge span under permitted label deletions; repeated span stabilization is absent from the final proof.")
    print("Relative quadratic extension, limiting prediction classes, majority trace bits, true-intersection truncation and the superlevel overlap proof are absent.")
    print("One preparation quota works at every sufficiently large size for all admissible inputs. Every attained predictor pair is used on both slices.")
    print("The two reciprocal zero parities use ambient rank. The rare-pair argument uses a positive conditional compatibility floor.")
    print("The graph proof uses finite labels for relative safety and counts four zero readings by rank on a bounded offset span.")
    print("Parseval selects the simultaneous query frequencies; one finite set minimum selects the exposed tensors.")
    print("Full keys determine all acceptance tests at a valid frame. The prepared overlap estimate uses linear partitions.")
    print("Two independent draws from one capped spreading frame law can have zero overlap for every complete option.")


if __name__ == "__main__":
    main()
