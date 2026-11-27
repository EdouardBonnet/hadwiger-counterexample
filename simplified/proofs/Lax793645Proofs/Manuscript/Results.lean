import Lax793645
import Lax793645Proofs.Manuscript.Publication
import Lax793645Proofs.Construction
import Lax793645Proofs.Simplifications.AffineTensorMoments
import Lax793645Proofs.Simplifications.MatchingNeighborhoods
import Lax793645Proofs.Simplifications.OrderedSlotCompletion
import Lax793645Proofs.Simplifications.CommonLinearFrequencies
import Lax793645Proofs.Simplifications.CoordinateQuadraticExtension
import Lax793645Proofs.Simplifications.CycleMarkedProfiles
import Lax793645Proofs.Simplifications.ExactSevenPredictions
import Lax793645Proofs.Simplifications.GenericStatusSpans
import Lax793645Proofs.Simplifications.IndependentSevenLists
import Lax793645Proofs.Simplifications.OneBaseProductHits
import Lax793645Proofs.Simplifications.OneCollisionCalendar
import Lax793645Proofs.Simplifications.OneConstruction
import Lax793645Proofs.Simplifications.OneDirectCappedFourier
import Lax793645Proofs.Simplifications.OneExactForbiddenPredictions
import Lax793645Proofs.Simplifications.OneFinitePhaseAlternative
import Lax793645Proofs.Simplifications.OneFinitePreparation
import Lax793645Proofs.Simplifications.OneFrameGeometry
import Lax793645Proofs.Simplifications.OneGenericCommonScores
import Lax793645Proofs.Simplifications.OneLeafMixtures
import Lax793645Proofs.Simplifications.OnePreparedOutcomes
import Lax793645Proofs.Simplifications.OneQueryLinearPartitions
import Lax793645Proofs.Simplifications.OneQuietEnd
import Lax793645Proofs.Simplifications.OneReciprocalRealization
import Lax793645Proofs.Simplifications.OneRetainedPredictors
import Lax793645Proofs.Simplifications.OneScalarRecipes
import Lax793645Proofs.Simplifications.OneSelectedObstructions
import Lax793645Proofs.Simplifications.OneSidedOverlap
import Lax793645Proofs.Simplifications.QuadraticColumnCounts
import Lax793645Proofs.Simplifications.QueryFourierSpectrum
import Lax793645Proofs.Simplifications.ReducedBinaryPrescriptions
import Lax793645Proofs.Simplifications.ReducedMixerExistence
import Lax793645Proofs.Simplifications.SelectedTensorSeparation
import Lax793645Proofs.Simplifications.TensorAtomIsolation
import Lax793645Proofs.Simplifications.TensorConfinement
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ExponentialGraphTransfer
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.ScalarStatusAlgebra
import Lax793645Proofs.Upstream.OAI.Combinatorics.HadwigerCounterexample.SumRankBounds

/-!
The proof terms used here come from the construction modules imported above.
The public statements use the same formulas and the public names for their data.
A named result used by a later proof appears as an explicit archive dependency.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

open Lean Elab Command

run_cmd do
  liftCoreM <| Lax793645Proofs.Manuscript.Publication.publish #[
    (`Lax793645Proofs.Simplifications.one_hole_sym,
     `Lax793645.TriangleFreeHoles.one_hole_sym,
     `Lax793645Proofs.Manuscript.Checked.TriangleFreeHoles.one_hole_sym),
    (`Lax793645Proofs.Simplifications.one_hole_irrefl,
     `Lax793645.TriangleFreeHoles.one_hole_irrefl,
     `Lax793645Proofs.Manuscript.Checked.TriangleFreeHoles.one_hole_irrefl),
    (`Lax793645Proofs.Simplifications.one_hole_triangle,
     `Lax793645.TriangleFreeHoles.one_hole_triangle,
     `Lax793645Proofs.Manuscript.Checked.TriangleFreeHoles.one_hole_triangle),
    (`Lax793645Proofs.Simplifications.ordinaryBit_support,
     `Lax793645.OrdinaryTesterSupport.ordinaryBit_support,
     `Lax793645Proofs.Manuscript.Checked.OrdinaryTesterSupport.ordinaryBit_support),
    (`Lax793645Proofs.Simplifications.OneConstruction.eventual_conflict_lower_bound,
     `Lax793645.FourHoles.eventual_conflict_lower_bound,
     `Lax793645Proofs.Manuscript.Checked.FourHoles.eventual_conflict_lower_bound),
    (`Lax793645Proofs.Simplifications.MatchingNeighborhoods.hitting_list,
     `Lax793645.MatchingNeighborhoods.hitting_list,
     `Lax793645Proofs.Manuscript.Checked.MatchingNeighborhoods.hitting_list),
    (`Lax793645Proofs.Simplifications.MatchingNeighborhoods.hitting_all_neighborhoods,
     `Lax793645.MatchingNeighborhoods.hitting_all_neighborhoods,
     `Lax793645Proofs.Manuscript.Checked.MatchingNeighborhoods.hitting_all_neighborhoods),
    (`Lax793645Proofs.Upstream.OAI.HadwigerCounterexample.transfer_scales,
     `Lax793645.MatchingExposure.transfer_scales,
     `Lax793645Proofs.Manuscript.Checked.MatchingExposure.transfer_scales),
    (`Lax793645Proofs.Simplifications.quadratic_column_mass,
     `Lax793645.QuadraticFrameCounts.quadratic_column_mass,
     `Lax793645Proofs.Manuscript.Checked.QuadraticFrameCounts.quadratic_column_mass),
    (`Lax793645Proofs.Simplifications.quadratic_column_partner,
     `Lax793645.QuadraticFrameCounts.quadratic_column_partner,
     `Lax793645Proofs.Manuscript.Checked.QuadraticFrameCounts.quadratic_column_partner),
    (`Lax793645Proofs.Simplifications.one_first_leaves,
     `Lax793645.ClosedPins.one_first_leaves,
     `Lax793645Proofs.Manuscript.Checked.ClosedPins.one_first_leaves),
    (`Lax793645Proofs.Simplifications.affineTensor_identities,
     `Lax793645.AffinePointMatrices.affineTensor_identities,
     `Lax793645Proofs.Manuscript.Checked.AffinePointMatrices.affineTensor_identities),
    (`Lax793645Proofs.Simplifications.selector_confinement,
     `Lax793645.SelectorConfinement.selector_confinement,
     `Lax793645Proofs.Manuscript.Checked.SelectorConfinement.selector_confinement),
    (`Lax793645Proofs.Simplifications.reshape_rank_le,
     `Lax793645.SelectorConfinement.reshape_rank_le,
     `Lax793645Proofs.Manuscript.Checked.SelectorConfinement.reshape_rank_le),
    (`Lax793645Proofs.Simplifications.tensor_atom_isolation,
     `Lax793645.SelectedAtoms.tensor_atom_isolation,
     `Lax793645Proofs.Manuscript.Checked.SelectedAtoms.tensor_atom_isolation),
    (`Lax793645Proofs.Simplifications.selected_tensor_independent_mod_cross,
     `Lax793645.SelectedAtoms.selected_tensor_independent_mod_cross,
     `Lax793645Proofs.Manuscript.Checked.SelectedAtoms.selected_tensor_independent_mod_cross),
    (`Lax793645Proofs.Simplifications.goodReducedMixers,
     `Lax793645.MixingMatrices.goodReducedMixers,
     `Lax793645Proofs.Manuscript.Checked.MixingMatrices.goodReducedMixers),
    (`Lax793645Proofs.Simplifications.choose_reduced_script,
     `Lax793645.ScalarPrescriptions.choose_reduced_script,
     `Lax793645Proofs.Manuscript.Checked.ScalarPrescriptions.choose_reduced_script),
    (`Lax793645Proofs.Simplifications.one_recipe_atoms,
     `Lax793645.ScalarPrescriptions.one_recipe_atoms,
     `Lax793645Proofs.Manuscript.Checked.ScalarPrescriptions.one_recipe_atoms),
    (`Lax793645Proofs.Simplifications.one_recipe_effective,
     `Lax793645.ScalarPrescriptions.one_recipe_effective,
     `Lax793645Proofs.Manuscript.Checked.ScalarPrescriptions.one_recipe_effective),
    (`Lax793645Proofs.Simplifications.coordinate_quadratic_extension,
     `Lax793645.CoordinateCompletion.coordinate_quadratic_extension,
     `Lax793645Proofs.Manuscript.Checked.CoordinateCompletion.coordinate_quadratic_extension),
    (`Lax793645Proofs.Simplifications.one_selected_obstructions,
     `Lax793645.FrozenConstraints.one_selected_obstructions,
     `Lax793645Proofs.Manuscript.Checked.FrozenConstraints.one_selected_obstructions),
    (`Lax793645Proofs.Simplifications.one_reciprocal_realization,
     `Lax793645.FrameRealization.one_reciprocal_realization,
     `Lax793645Proofs.Manuscript.Checked.FrameRealization.one_reciprocal_realization),
    (`Lax793645Proofs.Simplifications.one_collision_calendar,
     `Lax793645.QueryCollision.one_collision_calendar,
     `Lax793645Proofs.Manuscript.Checked.QueryCollision.one_collision_calendar),
    (`Lax793645Proofs.Simplifications.one_phase_alternative,
     `Lax793645.PhaseAlternative.one_phase_alternative,
     `Lax793645Proofs.Manuscript.Checked.PhaseAlternative.one_phase_alternative),
    (`Lax793645Proofs.Upstream.OAI.HadwigerCounterexample.no_cover_rank,
     `Lax793645.RankOfIndependentSums.no_cover_rank,
     `Lax793645Proofs.Manuscript.Checked.RankOfIndependentSums.no_cover_rank),
    (`Lax793645Proofs.Simplifications.OneDurable.coded_safety,
     `Lax793645.SafeCompatiblePairs.coded_safety,
     `Lax793645Proofs.Manuscript.Checked.SafeCompatiblePairs.coded_safety),
    (`Lax793645Proofs.Simplifications.one_finite_preparation,
     `Lax793645.PreparedUnits.one_finite_preparation,
     `Lax793645Proofs.Manuscript.Checked.PreparedUnits.one_finite_preparation),
    (`Lax793645Proofs.Simplifications.ordered_slot_completion,
     `Lax793645.OrderedSlotCompletion.ordered_slot_completion,
     `Lax793645Proofs.Manuscript.Checked.OrderedSlotCompletion.ordered_slot_completion),
    (`Lax793645Proofs.Simplifications.one_direct_capped_leaf_fourier,
     `Lax793645.FourierComparison.one_direct_capped_leaf_fourier,
     `Lax793645Proofs.Manuscript.Checked.FourierComparison.one_direct_capped_leaf_fourier),
    (`Lax793645Proofs.Simplifications.filtered_large_spectrum,
     `Lax793645.LargeFrequencies.filtered_large_spectrum,
     `Lax793645Proofs.Manuscript.Checked.LargeFrequencies.filtered_large_spectrum),
    (`Lax793645Proofs.Simplifications.one_query_all_filters_linear_partition,
     `Lax793645.FilteredQueryPartition.one_query_all_filters_linear_partition,
     `Lax793645Proofs.Manuscript.Checked.FilteredQueryPartition.one_query_all_filters_linear_partition),
    (`Lax793645Proofs.Simplifications.shared_leaf_frequencies,
     `Lax793645.SharedFrequencies.shared_leaf_frequencies,
     `Lax793645Proofs.Manuscript.Checked.SharedFrequencies.shared_leaf_frequencies),
    (`Lax793645Proofs.Simplifications.one_sided_projected_mend,
     `Lax793645.ProjectedOverlap.one_sided_projected_mend,
     `Lax793645Proofs.Manuscript.Checked.ProjectedOverlap.one_sided_projected_mend),
    (`Lax793645Proofs.Simplifications.one_generic_lightmap,
     `Lax793645.SupportScores.one_generic_lightmap,
     `Lax793645Proofs.Manuscript.Checked.SupportScores.one_generic_lightmap),
    (`Lax793645Proofs.Upstream.OAI.HadwigerCounterexample.StatusAnalysis.counter_score,
     `Lax793645.ScalarDuality.counter_score,
     `Lax793645Proofs.Manuscript.Checked.ScalarDuality.counter_score),
    (`Lax793645Proofs.Upstream.OAI.HadwigerCounterexample.StatusAnalysis.critic_nz,
     `Lax793645.ScalarDuality.critic_nz,
     `Lax793645Proofs.Manuscript.Checked.ScalarDuality.critic_nz),
    (`Lax793645Proofs.Simplifications.exact_seven_alternative,
     `Lax793645.SevenPredictions.exact_seven_alternative,
     `Lax793645Proofs.Manuscript.Checked.SevenPredictions.exact_seven_alternative),
    (`Lax793645Proofs.Simplifications.seven_prediction_pairs_card,
     `Lax793645.SevenPredictions.seven_prediction_pairs_card,
     `Lax793645Proofs.Manuscript.Checked.SevenPredictions.seven_prediction_pairs_card),
    (`Lax793645Proofs.Simplifications.OneExactOptions.witnessed_cost,
     `Lax793645.RareObstructions.witnessed_cost,
     `Lax793645Proofs.Manuscript.Checked.RareObstructions.witnessed_cost),
    (`Lax793645Proofs.Simplifications.one_attained_scalar_soluble,
     `Lax793645.PredictedScalarSystem.one_attained_scalar_soluble,
     `Lax793645Proofs.Manuscript.Checked.PredictedScalarSystem.one_attained_scalar_soluble),
    (`Lax793645Proofs.Simplifications.OneExactOptions.no_out,
     `Lax793645.SolublePairs.no_out,
     `Lax793645Proofs.Manuscript.Checked.SolublePairs.no_out),
    (`Lax793645Proofs.Simplifications.generic_status_band_stable,
     `Lax793645.LabelDeletion.generic_status_band_stable,
     `Lax793645Proofs.Manuscript.Checked.LabelDeletion.generic_status_band_stable),
    (`Lax793645Proofs.Simplifications.IndependentClub.seven_list,
     `Lax793645.FreshWitnessLists.seven_list,
     `Lax793645Proofs.Manuscript.Checked.FreshWitnessLists.seven_list),
    (`Lax793645Proofs.Simplifications.one_quiet_end,
     `Lax793645.UnpredictedOverlap.one_quiet_end,
     `Lax793645Proofs.Manuscript.Checked.UnpredictedOverlap.one_quiet_end),
    (`Lax793645Proofs.Simplifications.OneQuill.one_base_product_relative_hit,
     `Lax793645.BaseQueryHits.one_base_product_relative_hit,
     `Lax793645Proofs.Manuscript.Checked.BaseQueryHits.one_base_product_relative_hit),
    (`Lax793645Proofs.Simplifications.OneQuill.one_base_product_hit_calendar,
     `Lax793645.BaseQueryHits.one_base_product_hit_calendar,
     `Lax793645Proofs.Manuscript.Checked.BaseQueryHits.one_base_product_hit_calendar),
    (`Lax793645Proofs.Construction.arbitrarily_large_small_connected_matching,
     `Lax793645.Counterexample.arbitrarily_large_small_connected_matching,
     `Lax793645Proofs.Manuscript.Checked.Counterexample.arbitrarily_large_small_connected_matching)]

/--
---
conclusion: Lax793645.TriangleFreeHoles.one_hole_sym
---
The implementation is `one_hole_sym` in `OneFrameGeometry.lean`.
-/
theorem Lax793645Proofs.Manuscript.TriangleFreeHoles.one_hole_sym :
    (type_of% @Lax793645.TriangleFreeHoles.one_hole_sym) :=
  @Lax793645Proofs.Manuscript.Checked.TriangleFreeHoles.one_hole_sym

/--
---
conclusion: Lax793645.TriangleFreeHoles.one_hole_irrefl
---
The implementation is `one_hole_irrefl` in `OneFrameGeometry.lean`.
-/
theorem Lax793645Proofs.Manuscript.TriangleFreeHoles.one_hole_irrefl :
    (type_of% @Lax793645.TriangleFreeHoles.one_hole_irrefl) :=
  @Lax793645Proofs.Manuscript.Checked.TriangleFreeHoles.one_hole_irrefl

/--
---
conclusion: Lax793645.TriangleFreeHoles.one_hole_triangle
---
The implementation is `one_hole_triangle` in `OneFrameGeometry.lean`.
-/
theorem Lax793645Proofs.Manuscript.TriangleFreeHoles.one_hole_triangle :
    (type_of% @Lax793645.TriangleFreeHoles.one_hole_triangle) :=
  @Lax793645Proofs.Manuscript.Checked.TriangleFreeHoles.one_hole_triangle

/--
---
conclusion: Lax793645.OrdinaryTesterSupport.ordinaryBit_support
---
The implementation is `ordinaryBit_support` in `CycleMarkedProfiles.lean`.
-/
theorem Lax793645Proofs.Manuscript.OrdinaryTesterSupport.ordinaryBit_support :
    (type_of% @Lax793645.OrdinaryTesterSupport.ordinaryBit_support) :=
  @Lax793645Proofs.Manuscript.Checked.OrdinaryTesterSupport.ordinaryBit_support

/--
---
conclusion: Lax793645.FourHoles.eventual_conflict_lower_bound
---
The implementation is `eventual_conflict_lower_bound` in `OneConstruction.lean`.
-/
theorem Lax793645Proofs.Manuscript.FourHoles.eventual_conflict_lower_bound :
    (type_of% @Lax793645.FourHoles.eventual_conflict_lower_bound) :=
  @Lax793645Proofs.Manuscript.Checked.FourHoles.eventual_conflict_lower_bound

/--
---
conclusion: Lax793645.MatchingNeighborhoods.hitting_list
---
Average the probability of missing a heavy neighborhood over the reference law.
-/
theorem Lax793645Proofs.Manuscript.MatchingNeighborhoods.hitting_list :
    (type_of% @Lax793645.MatchingNeighborhoods.hitting_list) :=
  @Lax793645Proofs.Manuscript.Checked.MatchingNeighborhoods.hitting_list

/--
---
conclusion: Lax793645.MatchingNeighborhoods.hitting_all_neighborhoods
---
A nonempty exceptional set has uniform mass at least the reciprocal of the number of types.
-/
theorem Lax793645Proofs.Manuscript.MatchingNeighborhoods.hitting_all_neighborhoods :
    (type_of% @Lax793645.MatchingNeighborhoods.hitting_all_neighborhoods) :=
  @Lax793645Proofs.Manuscript.Checked.MatchingNeighborhoods.hitting_all_neighborhoods

/--
---
conclusion: Lax793645.MatchingExposure.transfer_scales
---
Condition on the most probable list. Trim the averaged matching law and apply supersaturation.
-/
theorem Lax793645Proofs.Manuscript.MatchingExposure.transfer_scales :
    (type_of% @Lax793645.MatchingExposure.transfer_scales) :=
  @Lax793645Proofs.Manuscript.Checked.MatchingExposure.transfer_scales

/--
---
conclusion: Lax793645.QuadraticFrameCounts.quadratic_column_mass
---
The implementation is `quadratic_column_mass` in `QuadraticColumnCounts.lean`.
-/
theorem Lax793645Proofs.Manuscript.QuadraticFrameCounts.quadratic_column_mass :
    (type_of% @Lax793645.QuadraticFrameCounts.quadratic_column_mass) :=
  @Lax793645Proofs.Manuscript.Checked.QuadraticFrameCounts.quadratic_column_mass

/--
---
conclusion: Lax793645.QuadraticFrameCounts.quadratic_column_partner
---
The implementation is `quadratic_column_partner` in `QuadraticColumnCounts.lean`.
-/
theorem Lax793645Proofs.Manuscript.QuadraticFrameCounts.quadratic_column_partner :
    (type_of% @Lax793645.QuadraticFrameCounts.quadratic_column_partner) :=
  @Lax793645Proofs.Manuscript.Checked.QuadraticFrameCounts.quadratic_column_partner

/--
---
conclusion: Lax793645.ClosedPins.one_first_leaves
---
The implementation is `one_first_leaves` in `OneLeafMixtures.lean`.
-/
theorem Lax793645Proofs.Manuscript.ClosedPins.one_first_leaves :
    (type_of% @Lax793645.ClosedPins.one_first_leaves) :=
  @Lax793645Proofs.Manuscript.Checked.ClosedPins.one_first_leaves

/--
---
conclusion: Lax793645.AffinePointMatrices.affineTensor_identities
---
The implementation is `affineTensor_identities` in `AffineTensorMoments.lean`.
-/
theorem Lax793645Proofs.Manuscript.AffinePointMatrices.affineTensor_identities :
    (type_of% @Lax793645.AffinePointMatrices.affineTensor_identities) :=
  @Lax793645Proofs.Manuscript.Checked.AffinePointMatrices.affineTensor_identities

/--
---
conclusion: Lax793645.SelectorConfinement.selector_confinement
---
The implementation is `selector_confinement` in `TensorConfinement.lean`.
-/
theorem Lax793645Proofs.Manuscript.SelectorConfinement.selector_confinement :
    (type_of% @Lax793645.SelectorConfinement.selector_confinement) :=
  @Lax793645Proofs.Manuscript.Checked.SelectorConfinement.selector_confinement

/--
---
conclusion: Lax793645.SelectorConfinement.reshape_rank_le
---
The implementation is `reshape_rank_le` in `TensorConfinement.lean`.
-/
theorem Lax793645Proofs.Manuscript.SelectorConfinement.reshape_rank_le :
    (type_of% @Lax793645.SelectorConfinement.reshape_rank_le) :=
  @Lax793645Proofs.Manuscript.Checked.SelectorConfinement.reshape_rank_le

/--
---
conclusion: Lax793645.SelectedAtoms.tensor_atom_isolation
---
The implementation is `tensor_atom_isolation` in `TensorAtomIsolation.lean`.
-/
theorem Lax793645Proofs.Manuscript.SelectedAtoms.tensor_atom_isolation :
    (type_of% @Lax793645.SelectedAtoms.tensor_atom_isolation) :=
  @Lax793645Proofs.Manuscript.Checked.SelectedAtoms.tensor_atom_isolation

/--
---
conclusion: Lax793645.SelectedAtoms.selected_tensor_independent_mod_cross
---
The implementation is `selected_tensor_independent_mod_cross` in `SelectedTensorSeparation.lean`.
-/
theorem Lax793645Proofs.Manuscript.SelectedAtoms.selected_tensor_independent_mod_cross :
    (type_of% @Lax793645.SelectedAtoms.selected_tensor_independent_mod_cross) :=
  @Lax793645Proofs.Manuscript.Checked.SelectedAtoms.selected_tensor_independent_mod_cross

/--
---
conclusion: Lax793645.MixingMatrices.goodReducedMixers
---
The implementation is `goodReducedMixers` in `ReducedMixerExistence.lean`.
-/
theorem Lax793645Proofs.Manuscript.MixingMatrices.goodReducedMixers :
    (type_of% @Lax793645.MixingMatrices.goodReducedMixers) :=
  @Lax793645Proofs.Manuscript.Checked.MixingMatrices.goodReducedMixers

/--
---
conclusion: Lax793645.ScalarPrescriptions.choose_reduced_script
---
The implementation is `choose_reduced_script` in `ReducedBinaryPrescriptions.lean`.
-/
theorem Lax793645Proofs.Manuscript.ScalarPrescriptions.choose_reduced_script :
    (type_of% @Lax793645.ScalarPrescriptions.choose_reduced_script) :=
  @Lax793645Proofs.Manuscript.Checked.ScalarPrescriptions.choose_reduced_script

/--
---
conclusion: Lax793645.ScalarPrescriptions.one_recipe_atoms
---
The implementation is `one_recipe_atoms` in `OneScalarRecipes.lean`.
-/
theorem Lax793645Proofs.Manuscript.ScalarPrescriptions.one_recipe_atoms :
    (type_of% @Lax793645.ScalarPrescriptions.one_recipe_atoms) :=
  @Lax793645Proofs.Manuscript.Checked.ScalarPrescriptions.one_recipe_atoms

/--
---
conclusion: Lax793645.ScalarPrescriptions.one_recipe_effective
---
The implementation is `one_recipe_effective` in `OneScalarRecipes.lean`.
-/
theorem Lax793645Proofs.Manuscript.ScalarPrescriptions.one_recipe_effective :
    (type_of% @Lax793645.ScalarPrescriptions.one_recipe_effective) :=
  @Lax793645Proofs.Manuscript.Checked.ScalarPrescriptions.one_recipe_effective

/--
---
conclusion: Lax793645.CoordinateCompletion.coordinate_quadratic_extension
---
The implementation is `coordinate_quadratic_extension` in `CoordinateQuadraticExtension.lean`.
-/
theorem Lax793645Proofs.Manuscript.CoordinateCompletion.coordinate_quadratic_extension :
    (type_of% @Lax793645.CoordinateCompletion.coordinate_quadratic_extension) :=
  @Lax793645Proofs.Manuscript.Checked.CoordinateCompletion.coordinate_quadratic_extension

/--
---
conclusion: Lax793645.FrozenConstraints.one_selected_obstructions
---
The implementation is `one_selected_obstructions` in `OneSelectedObstructions.lean`.
-/
theorem Lax793645Proofs.Manuscript.FrozenConstraints.one_selected_obstructions :
    (type_of% @Lax793645.FrozenConstraints.one_selected_obstructions) :=
  @Lax793645Proofs.Manuscript.Checked.FrozenConstraints.one_selected_obstructions

/--
---
conclusion: Lax793645.FrameRealization.one_reciprocal_realization
---
The implementation is `one_reciprocal_realization` in `OneReciprocalRealization.lean`.
-/
theorem Lax793645Proofs.Manuscript.FrameRealization.one_reciprocal_realization :
    (type_of% @Lax793645.FrameRealization.one_reciprocal_realization) :=
  @Lax793645Proofs.Manuscript.Checked.FrameRealization.one_reciprocal_realization

/--
---
conclusion: Lax793645.QueryCollision.one_collision_calendar
---
The implementation is `one_collision_calendar` in `OneCollisionCalendar.lean`.
-/
theorem Lax793645Proofs.Manuscript.QueryCollision.one_collision_calendar :
    (type_of% @Lax793645.QueryCollision.one_collision_calendar) :=
  @Lax793645Proofs.Manuscript.Checked.QueryCollision.one_collision_calendar

/--
---
conclusion: Lax793645.PhaseAlternative.one_phase_alternative
---
The implementation is `one_phase_alternative` in `OneFinitePhaseAlternative.lean`.
-/
theorem Lax793645Proofs.Manuscript.PhaseAlternative.one_phase_alternative :
    (type_of% @Lax793645.PhaseAlternative.one_phase_alternative) :=
  @Lax793645Proofs.Manuscript.Checked.PhaseAlternative.one_phase_alternative

/--
---
conclusion: Lax793645.RankOfIndependentSums.no_cover_rank
---
The implementation is `no_cover_rank` in `SumRankBounds.lean`.
-/
theorem Lax793645Proofs.Manuscript.RankOfIndependentSums.no_cover_rank :
    (type_of% @Lax793645.RankOfIndependentSums.no_cover_rank) :=
  @Lax793645Proofs.Manuscript.Checked.RankOfIndependentSums.no_cover_rank

/--
---
conclusion: Lax793645.SafeCompatiblePairs.coded_safety
---
The implementation is `coded_safety` in `OnePreparedOutcomes.lean`.
-/
theorem Lax793645Proofs.Manuscript.SafeCompatiblePairs.coded_safety :
    (type_of% @Lax793645.SafeCompatiblePairs.coded_safety) :=
  @Lax793645Proofs.Manuscript.Checked.SafeCompatiblePairs.coded_safety

/--
---
conclusion: Lax793645.PreparedUnits.one_finite_preparation
---
The implementation is `one_finite_preparation` in `OneFinitePreparation.lean`.
-/
theorem Lax793645Proofs.Manuscript.PreparedUnits.one_finite_preparation :
    (type_of% @Lax793645.PreparedUnits.one_finite_preparation) :=
  @Lax793645Proofs.Manuscript.Checked.PreparedUnits.one_finite_preparation

/--
---
conclusion: Lax793645.OrderedSlotCompletion.ordered_slot_completion
---
Copy the permitted upper slot pairs and transpose the strict upper part. Each piece has
rank at most the number of slots times the rank of the ordinary completion.
-/
theorem Lax793645Proofs.Manuscript.OrderedSlotCompletion.ordered_slot_completion :
    (type_of% @Lax793645.OrderedSlotCompletion.ordered_slot_completion) :=
  @Lax793645Proofs.Manuscript.Checked.OrderedSlotCompletion.ordered_slot_completion

/--
---
conclusion: Lax793645.FourierComparison.one_direct_capped_leaf_fourier
---
The implementation is `one_direct_capped_leaf_fourier` in `OneDirectCappedFourier.lean`.
-/
theorem Lax793645Proofs.Manuscript.FourierComparison.one_direct_capped_leaf_fourier :
    (type_of% @Lax793645.FourierComparison.one_direct_capped_leaf_fourier) :=
  @Lax793645Proofs.Manuscript.Checked.FourierComparison.one_direct_capped_leaf_fourier

/--
---
conclusion: Lax793645.LargeFrequencies.filtered_large_spectrum
---
The implementation is `filtered_large_spectrum` in `QueryFourierSpectrum.lean`.
-/
theorem Lax793645Proofs.Manuscript.LargeFrequencies.filtered_large_spectrum :
    (type_of% @Lax793645.LargeFrequencies.filtered_large_spectrum) :=
  @Lax793645Proofs.Manuscript.Checked.LargeFrequencies.filtered_large_spectrum

/--
---
conclusion: Lax793645.FilteredQueryPartition.one_query_all_filters_linear_partition
---
The implementation is `one_query_all_filters_linear_partition` in `OneQueryLinearPartitions.lean`.
-/
theorem Lax793645Proofs.Manuscript.FilteredQueryPartition.one_query_all_filters_linear_partition :
    (type_of% @Lax793645.FilteredQueryPartition.one_query_all_filters_linear_partition) :=
  @Lax793645Proofs.Manuscript.Checked.FilteredQueryPartition.one_query_all_filters_linear_partition

/--
---
conclusion: Lax793645.SharedFrequencies.shared_leaf_frequencies
---
The implementation is `shared_leaf_frequencies` in `CommonLinearFrequencies.lean`.
-/
theorem Lax793645Proofs.Manuscript.SharedFrequencies.shared_leaf_frequencies :
    (type_of% @Lax793645.SharedFrequencies.shared_leaf_frequencies) :=
  @Lax793645Proofs.Manuscript.Checked.SharedFrequencies.shared_leaf_frequencies

/--
---
conclusion: Lax793645.ProjectedOverlap.one_sided_projected_mend
---
The implementation is `one_sided_projected_mend` in `OneSidedOverlap.lean`.
-/
theorem Lax793645Proofs.Manuscript.ProjectedOverlap.one_sided_projected_mend :
    (type_of% @Lax793645.ProjectedOverlap.one_sided_projected_mend) :=
  @Lax793645Proofs.Manuscript.Checked.ProjectedOverlap.one_sided_projected_mend

/--
---
conclusion: Lax793645.SupportScores.one_generic_lightmap
---
The implementation is `one_generic_lightmap` in `OneGenericCommonScores.lean`.
-/
theorem Lax793645Proofs.Manuscript.SupportScores.one_generic_lightmap :
    (type_of% @Lax793645.SupportScores.one_generic_lightmap) :=
  @Lax793645Proofs.Manuscript.Checked.SupportScores.one_generic_lightmap

/--
---
conclusion: Lax793645.ScalarDuality.counter_score
---
The implementation is `counter_score` in `ScalarStatusAlgebra.lean`.
-/
theorem Lax793645Proofs.Manuscript.ScalarDuality.counter_score :
    (type_of% @Lax793645.ScalarDuality.counter_score) :=
  @Lax793645Proofs.Manuscript.Checked.ScalarDuality.counter_score

/--
---
conclusion: Lax793645.ScalarDuality.critic_nz
---
The implementation is `critic_nz` in `ScalarStatusAlgebra.lean`.
-/
theorem Lax793645Proofs.Manuscript.ScalarDuality.critic_nz :
    (type_of% @Lax793645.ScalarDuality.critic_nz) :=
  @Lax793645Proofs.Manuscript.Checked.ScalarDuality.critic_nz

/--
---
conclusion: Lax793645.SevenPredictions.exact_seven_alternative
---
The implementation is `exact_seven_alternative` in `ExactSevenPredictions.lean`.
-/
theorem Lax793645Proofs.Manuscript.SevenPredictions.exact_seven_alternative :
    (type_of% @Lax793645.SevenPredictions.exact_seven_alternative) :=
  @Lax793645Proofs.Manuscript.Checked.SevenPredictions.exact_seven_alternative

/--
---
conclusion: Lax793645.SevenPredictions.seven_prediction_pairs_card
---
The implementation is `seven_prediction_pairs_card` in `ExactSevenPredictions.lean`.
-/
theorem Lax793645Proofs.Manuscript.SevenPredictions.seven_prediction_pairs_card :
    (type_of% @Lax793645.SevenPredictions.seven_prediction_pairs_card) :=
  @Lax793645Proofs.Manuscript.Checked.SevenPredictions.seven_prediction_pairs_card

/--
---
conclusion: Lax793645.RareObstructions.witnessed_cost
---
The implementation is `witnessed_cost` in `OneExactForbiddenPredictions.lean`.
-/
theorem Lax793645Proofs.Manuscript.RareObstructions.witnessed_cost :
    (type_of% @Lax793645.RareObstructions.witnessed_cost) :=
  @Lax793645Proofs.Manuscript.Checked.RareObstructions.witnessed_cost

/--
---
conclusion: Lax793645.PredictedScalarSystem.one_attained_scalar_soluble
---
The implementation is `one_attained_scalar_soluble` in `OneRetainedPredictors.lean`.
-/
theorem Lax793645Proofs.Manuscript.PredictedScalarSystem.one_attained_scalar_soluble :
    (type_of% @Lax793645.PredictedScalarSystem.one_attained_scalar_soluble) :=
  @Lax793645Proofs.Manuscript.Checked.PredictedScalarSystem.one_attained_scalar_soluble

/--
---
conclusion: Lax793645.SolublePairs.no_out
---
The implementation is `no_out` in `OneExactForbiddenPredictions.lean`.
-/
theorem Lax793645Proofs.Manuscript.SolublePairs.no_out :
    (type_of% @Lax793645.SolublePairs.no_out) :=
  @Lax793645Proofs.Manuscript.Checked.SolublePairs.no_out

/--
---
conclusion: Lax793645.LabelDeletion.generic_status_band_stable
---
The implementation is `generic_status_band_stable` in `GenericStatusSpans.lean`.
-/
theorem Lax793645Proofs.Manuscript.LabelDeletion.generic_status_band_stable :
    (type_of% @Lax793645.LabelDeletion.generic_status_band_stable) :=
  @Lax793645Proofs.Manuscript.Checked.LabelDeletion.generic_status_band_stable

/--
---
conclusion: Lax793645.FreshWitnessLists.seven_list
---
The implementation is `seven_list` in `IndependentSevenLists.lean`.
-/
theorem Lax793645Proofs.Manuscript.FreshWitnessLists.seven_list :
    (type_of% @Lax793645.FreshWitnessLists.seven_list) :=
  @Lax793645Proofs.Manuscript.Checked.FreshWitnessLists.seven_list

/--
---
conclusion: Lax793645.UnpredictedOverlap.one_quiet_end
---
The implementation is `one_quiet_end` in `OneQuietEnd.lean`.
-/
theorem Lax793645Proofs.Manuscript.UnpredictedOverlap.one_quiet_end :
    (type_of% @Lax793645.UnpredictedOverlap.one_quiet_end) :=
  @Lax793645Proofs.Manuscript.Checked.UnpredictedOverlap.one_quiet_end

/--
---
conclusion: Lax793645.BaseQueryHits.one_base_product_relative_hit
---
The implementation is `one_base_product_relative_hit` in `OneBaseProductHits.lean`.
-/
theorem Lax793645Proofs.Manuscript.BaseQueryHits.one_base_product_relative_hit :
    (type_of% @Lax793645.BaseQueryHits.one_base_product_relative_hit) :=
  @Lax793645Proofs.Manuscript.Checked.BaseQueryHits.one_base_product_relative_hit

/--
---
conclusion: Lax793645.BaseQueryHits.one_base_product_hit_calendar
---
The implementation is `one_base_product_hit_calendar` in `OneBaseProductHits.lean`.
-/
theorem Lax793645Proofs.Manuscript.BaseQueryHits.one_base_product_hit_calendar :
    (type_of% @Lax793645.BaseQueryHits.one_base_product_hit_calendar) :=
  @Lax793645Proofs.Manuscript.Checked.BaseQueryHits.one_base_product_hit_calendar

/--
---
conclusion: Lax793645.Counterexample.arbitrarily_large_small_connected_matching
---
The implementation is `arbitrarily_large_small_connected_matching` in `Construction.lean`.
-/
theorem Lax793645Proofs.Manuscript.Counterexample.arbitrarily_large_small_connected_matching :
    (type_of% @Lax793645.Counterexample.arbitrarily_large_small_connected_matching) :=
  @Lax793645Proofs.Manuscript.Checked.Counterexample.arbitrarily_large_small_connected_matching
