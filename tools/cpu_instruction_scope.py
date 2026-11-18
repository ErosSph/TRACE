"""Explicit user-selected verification domains, not inferred DUT capabilities."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCOPES = ('rv32i38', 'pico29')
PICO_EXCLUDED = frozenset(('Lb', 'Lh', 'Lw', 'Lbu', 'Lhu', 'Sb', 'Sh', 'Sw', 'Fence_i'))


def select(plan, scope):
    if scope not in SCOPES:
        raise ValueError('unknown instruction scope: '+str(scope))
    excluded = PICO_EXCLUDED if scope == 'pico29' else frozenset()
    names = {row['instruction'] for row in plan['instructions']}
    if len(names) != 38 or not excluded <= names:
        raise ValueError('scope requires the complete original 38-instruction manifest')
    return dict(plan, instruction_scope=scope,
        original_manifest_size=38,
        instructions=[row for row in plan['instructions'] if row['instruction'] not in excluded],
        excluded_instructions=[dict(instruction=row['instruction'], status='out_of_scope',
            reason='explicit user scope; not a proof failure')
            for row in plan['instructions'] if row['instruction'] in excluded])


def for_input(ast_path, ast_module):
    """Match the exact registered input, never a substring or guessed CPU role."""
    path = Path(ast_path)
    path = (path if path.is_absolute() else ROOT/path).resolve()
    catalog = json.loads((ROOT/'framework/pending-rtl-inputs.json').read_text())
    matches = [row for row in catalog['designs']
        if (ROOT/row['ast']).resolve() == path and row['ast_module'] == ast_module]
    if len(matches) > 1:
        raise ValueError('ambiguous input catalog')
    return 'pico29' if matches and matches[0]['name'] == 'picorv32' else 'rv32i38'
