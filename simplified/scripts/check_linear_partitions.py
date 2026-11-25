#!/usr/bin/env python3
"""Check the linear comparison and predictor lemmas; audit final adoption separately."""
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path
from check_simplifications import declarations_in

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / 'proofs'
PREFIX = 'Lax793645Proofs.Simplifications.'
MODULES = ['FourCornerRank', 'BlockRankCompletion', 'CommonLinearFrequencies', 'CappedLinearRank', 'LinearFourier', 'GramKernelBounds', 'FourierNorm', 'InjectivityPolynomial', 'WeightedFourCorners', 'NominalBlockDeletion', 'LinearRelationFourier', 'PrescribedKernelGram', 'GramFourCorners', 'RetainedFourCornerBatches', 'NominalKernelTails', 'LowRankGramFourier', 'AffineQueryCorners', 'CappedLeafComparison', 'CappedLeafFourier', 'CornerPatternSum', 'CrossPatternSums', 'DependentFrameImages', 'GramPatternSum', 'HighRankBatchWeights', 'LinearQueryComparison', 'LinearSupportedTests', 'LinearTestPartitions', 'LowRankBatchWeights', 'MomentBudgetScales', 'MomentScaleAlgebra', 'NetworkKernelNormalization', 'NetworkSieveLaw', 'NominalNetworkFactors', 'NormalizedGramBatches', 'ProductKernelComparison', 'QueryCappedMoment', 'QueryHighMoment', 'QueryMomentDecay', 'QueryMomentExpansion', 'QueryWeightSupremum', 'RawBudgetExponents', 'RawFrameBatchBound', 'SimultaneousKernelSieve', 'UniformCornerBound', 'UniformRawBatchBound', 'BoundedOverlapTransfer', 'CappedInputStatusComparison', 'ColoredCutEnergy', 'ConditionalCellHits', 'FilteredColoredDensities', 'FilteredDensityEnergy', 'FilteredProjectionBounds', 'GramReferenceBias', 'GramReferenceFourier', 'LinearAdaptiveOverlap', 'LinearCellBounds', 'LinearCommonOverlap', 'LinearDensityRefinement', 'LinearPartitionAppend', 'LinearPartitionGeometry', 'LinearProjectionFourier', 'LinearReferenceProjection', 'LinearTestRefinement', 'PrintedStatusComparison', 'ProjectionRefinementBounds', 'QuadraticStatusFourier', 'QueryCoordinateLaws', 'QueryDensityRefinement', 'QueryFilteredComparison', 'QueryLinearEnergy', 'QueryLinearPartitions', 'QueryReferenceBias', 'QueryStatusWeights', 'RelativeDensityEnergy', 'SuccessfulCommonProjection', 'SuccessfulLinearQueries', 'AsymmetricCommonProjection', 'EquivariantProjection', 'ProjectedDensityMend', 'SuccessfulFiniteProjection', 'ClippedFiniteProjection', 'ClippedSuccessfulProjection', 'ClippingContraction', 'EquivariantRebate', 'LinearAdaptiveRebate', 'LinearPartitionPaints', 'ExactPaintComparisons', 'ClippedProductProjection', 'PairedFrameRowBounds', 'PreparedLinearRank', 'ExactBaseQueryComparison', 'ExactBaseQueryHits', 'ProductQueryCells', 'SuccessfulProductPartitions', 'LinearSuperlevels', 'LightQueryBounds']
MODULES += ['LinearCellCoordinates', 'LinearPredictorCertificates', 'LinearPalette', 'LinearPaintComparisons', 'LinearPredictionConditions']
MODULES += ['JointPredictorCoordinates', 'JointKeyFiberLaws', 'QueryCellRecentring',
            'CoherentQueryArrays', 'LinearScreenSlopes', 'LinearScreenContradiction',
            'LinearZeroDiscrepancy', 'LinearPreparedConsistency']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
COMPARISON = PREFIX + 'clipped_successful_product_projection'
REQUIRED = [PREFIX + name for name in (
    'query_high_moment', 'query_moment_decay', 'capped_leaf_comparison',
    'law_peek_dependent', 'simultaneous_relative_sieve_error',
    'full_pattern_sum_bound', 'patterned_block_rank_completion',
    'uniform_corner_nominal_tail', 'linear_supported_refinement', 'linear_test_refinement',
    'query_p_weights_norm', 'capped_input_status_comparison',
    'query_all_filters_linear_partition', 'successful_query_linear_partition',
    'linear_adaptive_overlap', 'linear_adaptive_rebate',
    'linear_reference_common_overlap')]
FORBIDDEN = ['Lax793645Proofs.Upstream.OAI.HadwigerCounterexample.' + name for name in (
    'Template.weakly', 'Template.plays_calendar', 'Template.shattered',
    'Template.controls', 'Template.legacy_controls', 'erosive', 'erosive_implementation')]


def dependency_check_code():
    code = '''
open Lean Elab Command
partial def visitComparisonDependencies (env : Environment) (name : Name) : StateM NameSet Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  if let some info := env.find? name then
    info.type.getUsedConstants.forM (visitComparisonDependencies env)
    if let some value := info.value? (allowOpaque := true) then
      value.getUsedConstants.forM (visitComparisonDependencies env)
    if let .inductInfo data := info then
      data.ctors.forM (visitComparisonDependencies env)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let seen := (visitComparisonDependencies env `COMPARISON).run {} |>.2
  for name in REQUIRED do
    unless env.contains name do throwError m!"Unknown comparison audit target: {name}"
  for name in ALL_NAMES do
    logInfo m!"COMPARISON_DEPENDENCY {name}: {seen.contains name}"
'''
    return code.replace('`COMPARISON', '`' + COMPARISON).replace(
        'REQUIRED', '[' + ', '.join('`' + n for n in REQUIRED) + ']').replace(
        'ALL_NAMES', '[' + ', '.join('`' + n for n in REQUIRED + FORBIDDEN) + ']')


def run(args):
    result = subprocess.run(args, cwd=PROOFS, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    paths = [PROOFS / 'Lax793645Proofs/Simplifications' / (name + '.lean') for name in MODULES]
    names = []
    for path in paths:
        code = path.read_text()
        assert not re.search(r'\b(sorry|admit|native_decide)\b', code), path
        assert not re.search(r'^\s*(axiom|unsafe)\b', code, re.M), path
        names.extend(declarations_in(code))
    print(run(['lake', 'build', *(PREFIX + name for name in MODULES)]), end='', flush=True)
    code = '\n'.join(['import Lean', *('import ' + PREFIX + m for m in MODULES),
                      *('#print axioms ' + n for n in names)]) + '\n' + dependency_check_code()
    with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
        f.write(code)
        path = Path(f.name)
    try:
        output = run(['lake', 'env', 'lean', str(path)])
    finally:
        path.unlink()
    checked = {name: sorted(a.strip() for a in axioms.split(',') if a.strip())
               for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        checked[name] = []
    assert set(checked) == set(names), output
    for name, axioms in checked.items():
        assert set(axioms) <= ALLOWED, (name, axioms)
    for name in REQUIRED:
        assert f'COMPARISON_DEPENDENCY {name}: true' in output, output
    for name in FORBIDDEN:
        assert f'COMPARISON_DEPENDENCY {name}: false' in output, output
    report = {
        'comparison_target': COMPARISON,
        'comparison_required_present': REQUIRED,
        'comparison_forbidden_absent': FORBIDDEN,
        'baseline': 'ff9383d',
        'scope': 'Retained-batch high moment, actual query statuses, all-filter leaf partitions, clipped common projection with pair-dependent filters, and concrete linear predictor consistency under the prepared marginal cap; final adoption is audited separately.',
        'theorems': checked,
        'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'still_required': ['natural-language rewrite of the integrated analytic replacement'],
    }
    (ROOT / 'references/linear-partitions-audit.json').write_text(
        json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(output, end='')
    print(f'CHECKED: {len(names)} theorems in {len(MODULES)} modules; only standard Lean axioms.')
    print("The clipped common projection and concrete predictor consistency are checked; check_integration.py separately audits final adoption.")


if __name__ == '__main__':
    main()
