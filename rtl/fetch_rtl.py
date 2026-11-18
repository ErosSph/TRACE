#!/usr/bin/env python3
"""Reproduce the exact RTL sources the TRACE proofs were imported from.

For every design in designs.json this script
  1. fetches the upstream repository at the pinned commit (git, shallow),
  2. copies the used files into <out>/<design>/ (upstream relative paths are kept),
  3. applies the TRACE fix patches (rtl/patches/<design>/),
  4. adds our wrapper files (rtl/wrappers/<design>/),
  5. checks the sha256 of every final file against designs.json.
Bzeeno is the exception: its RTL is exported from the module quotations in the TRACE Coq library
(rtl/tools/export_quoted_rtl.py) and then patched; nothing is downloaded for it.

Usage:
  python3 rtl/fetch_rtl.py                       # all designs into rtl/src/
  python3 rtl/fetch_rtl.py --design kronos --out /tmp/rtl
Exit status 0 only if every requested design reproduces bit-exactly.
Needs: python3 (stdlib) and git.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(*args, cwd):
    subprocess.run(['git', *args], cwd=cwd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)


def fetch(repo, commit, dest):
    dest.mkdir(parents=True, exist_ok=True)
    git('init', '-q', cwd=dest)
    git('remote', 'add', 'origin', repo, cwd=dest)
    git('fetch', '-q', '--depth', '1', 'origin', commit, cwd=dest)
    git('checkout', '-q', 'FETCH_HEAD', cwd=dest)


HUNK = re.compile(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@')


def apply_patch(patch_file, base_dir):
    """Apply a unified diff (paths a/<p>, b/<p>) under base_dir; every context line must match exactly."""
    lines = Path(patch_file).read_text().splitlines(keepends=True)
    i = 0
    while i < len(lines):
        if not lines[i].startswith('--- '):
            i += 1
            continue
        target = lines[i + 1][4:].strip().split('\t')[0]
        target = target[2:] if target.startswith('b/') else target
        path = base_dir / target
        old = path.read_text().splitlines(keepends=True)
        new, pos = [], 0
        i += 2
        while i < len(lines) and lines[i].startswith('@@'):
            m = HUNK.match(lines[i])
            n_old, n_new = int(m.group(2) or 1), int(m.group(4) or 1)
            start = int(m.group(1)) - 1 if n_old else int(m.group(1))
            new += old[pos:start]
            pos = start
            i += 1
            while i < len(lines) and (n_old > 0 or n_new > 0 or lines[i].startswith('\\')):
                tag, text = lines[i][:1], lines[i][1:]
                if tag in (' ', '-'):
                    n_old -= 1
                if tag in (' ', '+'):
                    n_new -= 1
                if tag == '\\':           # "\ No newline at end of file"
                    if new and new[-1].endswith('\n'):
                        new[-1] = new[-1][:-1]
                elif tag == '+':
                    new.append(text)
                else:
                    if pos >= len(old) or old[pos].rstrip('\n') != text.rstrip('\n'):
                        raise SystemExit(f'{patch_file}: context mismatch in {target} at line {pos + 1}')
                    if tag == ' ':
                        new.append(old[pos])
                    pos += 1
                i += 1
        new += old[pos:]
        path.write_text(''.join(new))


def build(name, d, out, coq_dir, workdir):
    dst = out / name
    if dst.exists():
        shutil.rmtree(dst)
    dst.mkdir(parents=True)
    if d.get('source_kind') == 'coq-quotation':
        srcs = []
        for s in d['coq_sources']:
            p = coq_dir / s['path']
            if not p.exists() or sha256(p) != s['sha256']:
                raise SystemExit(f'{name}: Coq source {p} missing or different from designs.json')
            srcs += ['--source', str(p)]
        subprocess.run([sys.executable, str(HERE / 'tools/export_quoted_rtl.py'), *srcs, '--output', str(dst)],
                       check=True, stdout=subprocess.DEVNULL)
        (dst / 'manifest.json').unlink(missing_ok=True)
    else:
        clone = workdir / name
        fetch(d['repository'], d['commit'], clone)
        for f in d['files']:
            (dst / f['local']).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(clone / f['upstream'], dst / f['local'])
    for p in d['patches']:
        apply_patch(HERE / p['file'], dst)
    for w in d['wrappers']:
        shutil.copyfile(HERE / w['file'], dst / w['local'])
    bad = [f['local'] for f in d['files'] + d['wrappers'] if sha256(dst / f['local']) != f['sha256']]
    files = d.get('verilator_files') or [f['local'] for f in d['wrappers'] + d['files']]
    (dst / 'verilator.f').write_text('\n'.join(d['verilator_args'] + ['--top-module', d['top_module']] + files) + '\n')
    return bad


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--design', action='append', help='design name (repeatable; default: all)')
    ap.add_argument('--out', type=Path, default=HERE / 'src')
    ap.add_argument('--coq-dir', type=Path, default=ROOT / 'src', help='TRACE Coq library root (for Bzeeno)')
    a = ap.parse_args()
    designs = json.load(open(HERE / 'designs.json'))
    names = a.design or list(designs)
    failed = 0
    with tempfile.TemporaryDirectory() as work:
        for n in names:
            try:
                bad = build(n, designs[n], a.out.resolve(), a.coq_dir.resolve(), Path(work))
            except (subprocess.CalledProcessError, SystemExit, OSError) as e:
                print(f'{n:14s} FAILED: {e}')
                failed += 1
                continue
            total = len(designs[n]['files']) + len(designs[n]['wrappers'])
            print(f'{n:14s} {"OK" if not bad else "HASH MISMATCH " + ", ".join(bad)}  ({total} files)')
            failed += bool(bad)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
