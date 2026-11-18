"""Aggregate dependency audits without omitting a single exported constant.

This is independent of CPU names, signal IDs, instruction sets and proof tactics.
Coq still checks every original declaration. A nested pair stores ALL fully
generalized constants; Print Assumptions traverses their dependency union once.
The caller must validate the output and retain kernel and exact-type checks.
Pair type arguments can reveal additional type dependencies for exotic exports;
they are not suppressed. An unchanged-policy A/B test must compare actual sets,
and normal acceptance must reject any unexpected extra axiom.
"""
import hashlib
import re

SYMBOL = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*')
PRINT = re.compile(r'(?m)^Print Assumptions ([A-Za-z_][A-Za-z0-9_.]*)\.[ \t]*$')


def aggregate(source, exports):
    exports = list(exports)
    if not exports or len(set(exports)) != len(exports) or not all(SYMBOL.fullmatch(n) for n in exports):
        raise ValueError('nonempty, unique, qualified Coq export names required')
    commands = list(PRINT.finditer(source))
    if [m[1] for m in commands] != exports:
        raise ValueError('audit list must cover every original export, in order')
    prefix = source[:commands[0].start()]
    suffix = source[commands[0].start():]
    expected = ''.join('Print Assumptions '+n+'.\n' for n in exports)
    if suffix.strip() != expected.strip():
        raise ValueError('only the final original audit commands may be replaced')
    key = hashlib.sha256(expected.encode()).hexdigest()[:16]
    name = 'checked_export_dependency_union_' + key
    if re.search(r'\b'+name+r'\b', source):
        raise ValueError('audit constant collision')
    body = 'tt'
    for symbol in reversed(exports):
        body = '(@'+symbol+', '+body+')'
    addition = 'Definition '+name+' := '+body+'.\nPrint Assumptions '+name+'.\n'
    return prefix+addition, dict(method='all-export nested-pair dependency union',
        bundle=name, covered_exports=exports, original_audit_count=len(exports),
        resulting_audit_count=1, original_prefix_sha256=hashlib.sha256(prefix.encode()).hexdigest(),
        original_source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        original_prefix_unchanged=True, drops_type_checks=False, drops_kernel_checks=False)


def original_prefix(source):
    commands = list(PRINT.finditer(source))
    if not commands:
        raise ValueError('missing original audit footer')
    return source[:commands[0].start()]
