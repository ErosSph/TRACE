"""Pinned-source elaboration and candidate symbol binding; NOT translation proof.

Use the project-private CPython pyslang environment inside activated conda TP.
Reject unhandled frontend flags rather than guessing preprocessing settings.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def configuration(report):
    files = report['source_hashes']
    for item in files:
        if sha(item['path']) != item['sha256']:
            raise ValueError('source changed: ' + item['path'])
    cmd = report['command']
    top = cmd[cmd.index('--top-module') + 1]
    expected = ['verilator', '--xml-only', '--xml-output',
                cmd[cmd.index('--xml-output') + 1], '--Mdir',
                cmd[cmd.index('--Mdir') + 1], '--top-module', top,
                '-Wno-fatal', '-Wno-BLKANDNBLK',
                *[f['path'] for f in files]]
    if cmd != expected:
        raise ValueError('unhandled configuration: explicit flag adapter required')
    return dict(top=top, defines=[], include_dirs=[], parameter_overrides=[],
                source_hashes=files, original_command=cmd)


def bind(table, symbols):
    by_path = {}
    for symbol in symbols:
        if symbol['path'] in by_path:
            raise ValueError('ambiguous elaborated symbol identity')
        by_path[symbol['path']] = symbol
    result = []
    for field in table:
        symbol = by_path.get(field['path'])
        if symbol is None:
            raise ValueError('missing symbol: ' + field['path'])
        if (symbol['width'], symbol['line']) != (field['width'], field['source_line']):
            raise ValueError('width/location mismatch: ' + field['path'])
        result.append(dict(**symbol, coq_root=field['id'],
                           status='candidate_identity_not_semantic_equivalence'))
    return result


def analyze(report_path, ast_path, output):
    import pyslang as slang
    report = json.loads(Path(report_path).read_text())
    config = configuration(report)
    digest = hashlib.sha256(json.dumps(report['source_hashes'], sort_keys=True).encode()).hexdigest()
    source = Path(ast_path).read_text()
    expected = re.search(r'Definition source_tree_sha256 : string := "([a-f0-9]+)"', source)
    if expected is None or expected[1] != digest:
        raise ValueError('Coq AST source manifest mismatch')
    options = slang.ast.CompilationOptions()
    options.topModules = {config['top']}
    compilation = slang.ast.Compilation(slang.Bag([options]))
    for file in config['source_hashes']:
        compilation.addSyntaxTree(slang.syntax.SyntaxTree.fromFile(file['path']))
    root = compilation.getRoot()
    diagnostics = slang.DiagnosticEngine.reportAll(compilation.sourceManager, compilation.getAllDiagnostics())
    if compilation.hasIssuedErrors:
        raise ValueError('elaboration errors: ' + diagnostics)
    symbols = []
    def visit(node):
        if isinstance(node, slang.ast.Symbol) and node.isValue and hasattr(node, 'type'):
            sm = compilation.sourceManager
            symbols.append(dict(path=node.hierarchicalPath, kind=str(node.kind),
                                width=node.type.bitWidth, signed=node.type.isSigned,
                                type=str(node.type), file=str(Path(sm.getFileName(node.location)).resolve()),
                                line=sm.getLineNumber(node.location),
                                syntax=str(node.syntax) if node.syntax is not None else None))
    root.visit(visit)
    bindings = bind(report['signal_table'], symbols)
    from cpu_pyslang_cdfg import Graph
    graph = Graph(compilation, bindings).extract(root)
    result = dict(config=config, pyslang_version=slang.__version__, ast_sha256=sha(ast_path),
                  import_report=str(Path(report_path).resolve()),
                  report_sha256=sha(report_path), symbols=bindings,
                  diagnostics=diagnostics, elaboration_passed=True,
                  translation_equivalence_proved=False, complete_R_generated=False,
                  itree_refinement_proved=False,
                  obligations=['typed expression and control/state edge extraction',
                               'RTL-to-Coq expression and scheduling correspondence',
                               'ISA operand freshness and result relation',
                               'joint preservation and progress'])
    out = Path(output)
    out.mkdir(parents=True, exist_ok=False)
    (out/'binding.json').write_text(json.dumps(result, indent=2)+'\n')
    (out/'diagnostics.log').write_text(diagnostics)
    (out/'cdfg.json').write_text(json.dumps(graph, indent=2)+'\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for arg in ['report', 'ast', 'output']:
        p.add_argument('--'+arg, required=True, type=Path)
    args = p.parse_args()
    result = analyze(args.report, args.ast, args.output)
    print(json.dumps(dict(elaboration_passed=True, bound_symbols=len(result['symbols']),
                         translation_equivalence_proved=False)))
