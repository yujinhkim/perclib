#!/usr/bin/env python3
"""Conservative D-24 proof-only gate, selected by the PR label `proof`."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = set('def abbrev opaque axiom axioms constant constants inductive coinductive structure '
                'class instance notation syntax macro macro_rules elab elab_rules initialize '
                'builtin_initialize register_option register_builtin_option attribute export '
                'run_cmd run_elab run_tac deriving tag'.split())


def code_without_literals(text):
    """Erase nested comments and string literals before the conservative token check."""
    result, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if text.startswith('/-', i):
            depth = 1
            i += 2
            result.append(' ')
            continue
        if text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            continue
        raw = re.match(r'r(#+)?"', text[i:])
        if raw:
            closing = '"' + (raw[1] or '')
            end = text.find(closing, i + len(raw[0]))
            if end < 0:
                raise ValueError('Unterminated raw string')
            i = end + len(closing)
            result.append(' ')
            continue
        if text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == '\\' else 1
            if i >= len(text):
                raise ValueError('Unterminated string')
            i += 1
            result.append(' ')
            continue
        result.append(text[i])
        i += 1
    if depth:
        raise ValueError('Unterminated comment')
    return ''.join(result)


def check_paths_and_source(changes):
    for path, source in changes.items():
        p = Path(path)
        if p.suffix != '.lean' or p.name in ('Basic.lean', 'Defs.lean'):
            raise ValueError(f'Proof PR touches an interface/non-Lean file: {path}')
        code = code_without_literals(source or '')
        if path == 'PercLib.lean':
            if any(line.strip() and not re.fullmatch(
                    r'(?:module|(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?[\w.]+)',
                    line.strip()) for line in code.splitlines()):
                raise ValueError('The root may change imports only in a proof PR')
        bad = FORBIDDEN.intersection(re.findall(r'[A-Za-z_][A-Za-z0-9_]*', code))
        if bad:
            raise ValueError(f'Interface/metaprogramming tokens in {path}: {sorted(bad)}')


def compiled_interfaces(raw):
    return {d['name']: {k: d[k] for k in
            ('kind', 'module', 'public', 'universes', 'type', 'value', 'related')}
            for d in raw['declarations'] if d['kind'] != 'theorem'}


def tagged_statements(raw):
    return {d['name']: {k: d[k] for k in ('tag', 'type', 'statement_expr')}
            for d in raw['declarations'] if d['tag'] is not None}


def check_compiled(base, head):
    before, after = compiled_interfaces(base), compiled_interfaces(head)
    changed = [n for n in sorted(before.keys() | after.keys()) if before.get(n) != after.get(n)]
    if changed:
        raise ValueError('Compiled non-theorem declarations changed: ' + ', '.join(changed))
    if tagged_statements(base) != tagged_statements(head):
        raise ValueError('Tagged statements/associations changed; interface review required')


def command(*args, cwd=ROOT, capture=False):
    if capture:
        return subprocess.check_output(args, cwd=cwd, text=True)
    subprocess.run(args, cwd=cwd, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--event', type=Path, default=os.environ.get('GITHUB_EVENT_PATH'))
    parser.add_argument('--head-raw', type=Path, default=Path('.lake/manifest-raw.json'))
    args = parser.parse_args()
    event = json.loads(args.event.read_text()) if args.event else {}
    pr = event.get('pull_request')
    if not pr or 'proof' not in {x['name'] for x in pr.get('labels', [])}:
        print('Interface/review lane: no proof-only classification requested.')
        return
    base = pr['base']['sha']
    if not re.fullmatch('[0-9a-f]{40}', base):
        raise ValueError('Invalid base commit')
    if subprocess.run(['git', 'cat-file', '-e', base + '^{commit}'], cwd=ROOT,
                      stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode:
        command('git', 'fetch', '--no-tags', 'origin', base)
    paths = command('git', 'diff', '--name-only', '--no-renames', base, 'HEAD', capture=True).splitlines()
    changes = {p: (ROOT / p).read_text() if (ROOT / p).exists() else None for p in paths}
    check_paths_and_source(changes)
    # Isolated checkout/cache; builds run sequentially in this job. Never mutate the head build.
    temporary = tempfile.mkdtemp(prefix='perclib-proof-base-')
    checkout = Path(temporary) / 'base'
    try:
        command('git', 'worktree', 'add', '--detach', str(checkout), base)
        command('cp', '-a', '--reflink=auto', str(ROOT / '.lake'), str(checkout / '.lake'))
        command('lake', 'exe', 'cache', 'get', cwd=checkout)
        command('lake', 'build', '--wfail', cwd=checkout)
        raw = command('lake', 'env', 'lean', '-R', str(ROOT), '--run', str(ROOT / 'scripts/ExtractManifest.lean'),
                      cwd=checkout, capture=True)
        check_compiled(json.loads(raw), json.loads(args.head_raw.read_text()))
        print(f'Proof-only gate passed against actual base {base}; no compiled interface changes.')
    finally:
        if checkout.exists():
            command('git', 'worktree', 'remove', '--force', str(checkout))
        shutil.rmtree(temporary, ignore_errors=True)


if __name__ == '__main__':
    main()
