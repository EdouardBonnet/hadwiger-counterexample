#!/usr/bin/env python3
"""Audit quadratic construction lemmas; final proof adoption is checked separately."""
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path
from check_simplifications import declarations_in, CLOSED

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / 'proofs'
PREFIX = 'Lax793645Proofs.Simplifications.'
MODULES = [
    "QuadraticColumnCounts", "QuadraticFrameSymmetry", "RowSupportProbability",
    "ConstantRetention", "OneGenericQueryBounds", "OneGenericLeafScores",
    "OneGenericSimultaneousScores", "OneGenericPopulationScores", "OneGenericCommonScores",
    "OneGenericFiniteComparison", "OneGenericPositiveOptions",
    'CoordinateQuadraticBaseline',
    'CoordinateQuadraticCorrection',
    'CoordinateQuadraticExtension',
    'ClosedPinStep',
    'QuadraticKernelIntersection',
    'RelativeQuadraticKernel',
    'QuadraticRadicalCompression',
    'RelativeQuadraticRank',
    'RelativeQuadraticCompression',
    'QuadraticOneVector',
    'QuadraticEmbedding',
    'RelativeQuadraticExtension',
    'HyperbolicExtension',
    'QuadraticFrameCounts',
    'RelativeQuadraticBaseline',
    'ClosedBlockPins',
    'HyperbolicCoordinates',
    'OneFrameGeometry',
    'OneFrameLaws',
    'QuadraticChannelFrames',
    'QuadraticChannelRealization',
    'QuadraticCutAnnihilators',
    'QuadraticCutChannels',
    'QuadraticCutCompression',
    'QuadraticCutSolvability',
    'QuadraticFrameLowerBound',
    'QuadraticFrameMoves',
    'QuadraticFrozenFrames',
    'QuadraticImageCaps',
    'QuadraticMomentMaps',
    'QuadraticObservationBounds',
    'QuadraticOrbitLaws',
    'QuadraticPairCompletion',
    'QuadraticProtectedAnnihilators',
    'QuadraticRankReduction',
    'QuadraticReciprocalTable',
    'QuadraticSelectedChannels',
    'QuadraticTargetSolvability',
    'QuadraticTransvections',
    'ClosedImagePartitions',
    'ClosedImagePeeling',
    'ClosedPinCompletion',
    'CoordinatePinClosure',
    'ImageCellConditioning',
    'ImageGramCharacters',
    'ImageGramHits',
    'ImagePinFamilies',
    'ImageTupleBounds',
    'JointBlockKernel',
    'JointChannelReplacement',
    'JointQuadraticBlocks',
    'JointQuadraticChannels',
    'JointQuadraticCompression',
    'JointQuadraticCuts',
    'JointQuadraticObstructions',
    'JointQuadraticRank',
    'JointQuadraticSpace',
    'JointSelectedChannels',
    'JointSelectedReplacement',
    'OneChannelLaws',
    'OneChannelCoordinates',
    'OneChannelImageBounds',
    'OneChannelTests',
    'OneClosedImagePartitions',
    'OneClosedPinLaws',
    'OneEndpointPins',
    'OneFrameCoordinates',
    'OneFrozenTables',
    'OneGramHits',
    'OneKeyPins',
    'OnePhaseLaws',
    'OnePhaseMomentBounds',
    'OnePinInjection',
    'OneRealizedHits',
    'OneReciprocalRealization',
    'OneUnaryRecords',
    'OneUnitCollisions',
    'OneUnitGeometry',
    'QuadraticPinCaps',
    'QuadraticProtectedCuts',
    'QuadraticTableCoordinates',
    'QuadraticUnitTables',
    'FreeChannelCoordinates',
    'FreeChannelMarginals',
    'FreeCoordinateConditioning',
    'FreeLinearExtensions',
    'ImagePinCaps',
    'IndependentInjectionWitnesses',
    'NamedInjectionTransfer',
    'OneCoverGlimpses',
    'OneEffectiveSpaces',
    'OneFreeChannelLaws',
    'OneGradientTargets',
    'OneImagePinCaps',
    'OneInjectionBudget',
    'OneInjectionCalendar',
    'OneInjectionTail',
    'OneInjectionTransfer',
    'OneKeyPinSpaces',
    'OnePhaseActionLaws',
    'OnePinProtection',
    'OnePrimalImageBounds',
    'OneProtectedKeys',
    'OneScalarRealization',
    'OneScalarRecipes',
    'OneSelectedObstructions',
    'OneSelectedRealization',
    'QuadraticFreeChannelLaws',
    'QuadraticPhaseActionLaws',
    'QuadraticPhaseActions',
    'SymmetricOffsets',
    'ImageSeparatedObservations',
    'OneAdaptiveRecordBounds',
    'OneCoverSeparation',
    'OneDualImages',
    'OneFinitePhaseAlternative',
    'OneFrequentPhaseTests',
    'OneIndependentTestWitnesses',
    'OneMarginalPhaseBounds',
    'OneMarkedPhaseRecords',
    'OneOffsetFourierBounds',
    'OnePhaseAlternativeSupport',
    'OnePhaseBudgets',
    'OnePhaseCalendar',
    'OnePhaseCoefficients',
    'OnePhaseHeat',
    'OnePhaseProbeBounds',
    'OneProbeGrowth',
    'OneRawImageCalendar',
    'OneSingletonPhaseTests',
    'OneSupportedPhaseLaws',
    'OneSymmetricOffsets',
    'SymmetricOffsetRecords',
    'SymmetricPhaseEnergy',
]
MODULES = sorted(set(MODULES) | {p.stem for p in (PROOFS / 'Lax793645Proofs/Simplifications').glob('*.lean') if p.stem.startswith(('One', 'Quadratic', 'Joint', 'Image', 'Reduced', 'CycleMixer'))})
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


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
    proof_modules = sorted({name.rsplit('.', 1)[0] for name in CLOSED.values()})
    print(run(['lake', 'build', *(PREFIX + name for name in MODULES), *proof_modules]), end='', flush=True)
    code = '\n'.join([*('import ' + PREFIX + m for m in MODULES), *('import ' + m for m in proof_modules),
                      *('#print axioms ' + n for n in names + list(CLOSED.values()))]) + '\n'
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
    assert set(checked) == set(names) | set(CLOSED.values()), output
    raw = dict(checked)
    def expand(axioms, stack=()):
        result = set()
        for axiom in axioms:
            if axiom in ALLOWED:
                result.add(axiom)
            else:
                assert axiom in CLOSED and axiom not in stack, (axiom, stack)
                result |= expand(raw[CLOSED[axiom]], (*stack, axiom))
        return result
    checked = {name: sorted(expand(raw[name])) for name in names}
    report = {
        'baseline': 'a8fb678',
        'scope': 'The one-frame construction through the unchanged graph theorem: closed-pin preparation, quadratic realization and counts, retained-column Fourier comparison, linear partitions, both prediction branches, reduced mixers and parameter existence. Adoption is audited by check_integration.py.',
        'theorems': checked,
        'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'still_required': [],
        'raw_axioms': raw,
        'statement_proofs': CLOSED,
    }
    (ROOT / 'references/quadratic-foundations-audit.json').write_text(
        json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(output, end='')
    print(f'CHECKED: {len(checked)} distinct theorems in {len(MODULES)} modules; only standard Lean axioms.')
    print('The one-frame proof reaches the unchanged graph theorem; the separate dependency audit checks its adoption.')


if __name__ == '__main__':
    main()
