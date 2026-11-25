#!/usr/bin/env python3
"""Join a compiled Lean snapshot to W-1 tags. See scripts/MANIFEST.md."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

SCHEMA = 'perclib-statement-v1'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def references(expr):
    if not isinstance(expr, list) or not expr:
        return []
    if expr[0] == 'const':
        return [expr[1]]
    result = [expr[1]] if expr[0] == 'proj' else []
    for child in expr[1:]:
        result.extend(references(child))
    return result


def body(d):
    """A theorem's proof arrives as its referenced constants only (`proof_constants`)."""
    return d['proof_constants'] if d['kind'] == 'theorem' else d['value']


def body_references(d):
    if d['kind'] == 'theorem':
        return list(d['proof_constants'] or [])
    return references(d['value'])


def prop_valued(d):
    # Lean reduces the telescope/codomain; a raw syntax test would misclassify aliases.
    return d['prop_valued']


def statement_definition(d):
    return d['kind'] == 'definition' and prop_valued(d)


def proposition(d):
    expr = d['statement_expr']
    if expr is None:
        raise ValueError(f"Missing statement body: {d['name']}")
    return expr


def is_pair(statement, proof):
    """D-16: proof type is exactly the statement applied to its own telescope."""
    typ, spec = proof['type'], statement['type']
    count = 0
    while spec[0] == 'forall':
        if typ[0] != 'forall' or typ[1:3] != spec[1:3]:
            return False
        count += 1
        typ, spec = typ[3], spec[3]
    args = []
    while typ[0] == 'app':
        args.insert(0, typ[2])
        typ = typ[1]
    return (typ[0] == 'const' and typ[1] == statement['name']
            and args == [['bvar', n] for n in reversed(range(count))]
            and proof['universes'] == statement['universes']
            and typ[2] == [['param', n] for n in range(statement['universes'])])


def frontier(seeds, decls, associations, self_tag):
    pending, visited, result = list(seeds), set(), set()
    while pending:
        name = pending.pop()
        if name in visited:
            continue
        visited.add(name)
        if name in associations:
            tag = associations[name]
            if tag != self_tag:
                result.add(tag)
            continue
        if name in decls:
            d = decls[name]
            pending.extend(references(d['type']) + body_references(d) + d['related'])
    return sorted(result)


def fingerprint(expr, decls, context):
    """Name-independent rooted graph, numbering definitions by first structural encounter.

    Cycles terminate through references to assigned indices. Bound and universe parameter
    names were erased by Lean. Theorem proof bodies are excluded; definitional bodies,
    inductives/constructors and all types remain part of the statement closure.
    """
    ids, records = {}, []
    def reference(name):
        if name not in decls:
            return ['external', name]
        if name not in ids:
            ids[name] = len(records)
            records.append(None)
            d = decls[name]
            record = [d['kind'], d['universes'], encode(d['type'])]
            if d['kind'] in ('definition', 'opaque'):
                if d['value'] is None:
                    raise ValueError(f'Missing definition body: {name}')
                record.append(encode(d['value']))
            record.append([reference(n) for n in d['related']])
            records[ids[name]] = record
        return ['project', ids[name]]
    def encode(e):
        if not isinstance(e, list):
            return e
        if e and isinstance(e[0], str) and e[0].startswith('invalid-'):
            raise ValueError('Unresolved expression in compiled declaration')
        if e and e[0] == 'const':
            return ['const', reference(e[1]), e[2]]
        if e and e[0] == 'proj':
            return ['proj', reference(e[1]), e[2], encode(e[3])]
        return [encode(x) for x in e]
    root = encode(expr)
    payload = [SCHEMA, context, root, records]
    return hashlib.sha256(json.dumps(payload, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest()


def input_debts(expr, decls):
    pending, seen, debts = references(expr), set(), set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if name.split('.')[-1].endswith('Input'):
            debts.add(name)
        if name in decls:
            d = decls[name]
            pending += references(d['type'])
            if d['kind'] == 'definition':
                pending += references(d['value'])
    return sorted(debts)


def build(raw, catalog, context):
    decls = {d['name']: d for d in raw['declarations']}
    if len(decls) != len(raw['declarations']):
        raise ValueError('Duplicate declaration in snapshot')
    groups, associations = {}, {}
    for d in decls.values():
        tag = d['tag']
        if tag is None:
            continue
        if d['kind'] not in ('definition', 'theorem', 'opaque'):
            raise ValueError(f'Unsupported tagged declaration kind {d["kind"]}: {d["name"]}')
        if d['kind'] == 'opaque' and prop_valued(d):
            raise ValueError(f'Opaque proposition is unsupported by D-16: {d["name"]}')
        if not re.fullmatch('[0-9A-Z]{4}', tag) or tag not in catalog:
            raise ValueError(f'Unknown, withdrawn or absent wiki tag: {tag}')
        groups.setdefault(tag, []).append(d)
        associations[d['name']] = tag
    entries = []
    for tag, source in sorted(catalog.items()):
        ds = groups.get(tag, [])
        entry = {'tag': tag, **source, 'declarations': [], 'proof_status': 'unformalised'}
        if not ds:
            entries.append(entry)
            continue
        statements = [d for d in ds if statement_definition(d)]
        proofs = [d for d in ds if d['kind'] == 'theorem']
        if len(ds) > 1 and not (len(ds) == 2 and len(statements) == len(proofs) == 1
                               and is_pair(statements[0], proofs[0])):
            raise ValueError(f'Incompatible duplicate tag: {tag}')
        d = statements[0] if statements else ds[0]
        stmt = proposition(d) if statements else d['type']
        fingerprint_expr = (['definition', stmt, d['value']]
                            if d['kind'] in ('definition', 'opaque') and not statements else stmt)
        proof = proofs[0] if proofs else None
        if any(x['kind'] in ('definition', 'theorem', 'opaque') and body(x) is None for x in ds):
            raise ValueError(f'Missing body for {tag}')
        axioms = sorted(set().union(*(set(x['axioms']) for x in ds)))
        if set(axioms) - ALLOWED:
            raise ValueError(f'Forbidden axioms for {tag}: {set(axioms) - ALLOWED}')
        debts = input_debts(stmt, decls)
        status = 'statement-only' if statements and proof is None else ('proved-modulo' if debts else 'proved')
        proof_body = proof if proof else (None if statements else d)
        for x in sorted(ds, key=lambda x: x['name']):
            path = x['module'].replace('.', '/') + '.lean'
            entry['declarations'].append({'name': x['name'], 'kind': x['kind'],
                'type': x['display_type'], 'file': path, 'line': x['line']})
        entry.update(proof_status=status, axioms=axioms, inputs=debts,
            statement=d['display_statement'] if statements else d['display_type'],
            fingerprint={'schema': SCHEMA, 'sha256': fingerprint(fingerprint_expr, decls, context)},
            dependencies={'statement': frontier(references(stmt), decls, associations, tag),
                          'proof': frontier((body_references(proof_body) if proof_body else [])
                                            + ([] if statements else d['related']),
                                            decls, associations, tag)})
        entries.append(entry)
    return {'schema': 'perclib-manifest-v1', 'context': context, 'assertions': entries}


def catalog_from(root):
    # Use W-1's own parser and validator; never silently accept a divergent anchor grammar.
    code = '''import {readArticles, readRegistry, validateTags} from './wiki/scripts/articles.mjs';
console.log(JSON.stringify(validateTags(await readArticles(), await readRegistry())));'''
    items = json.loads(subprocess.check_output(['node', '--input-type=module', '-e', code], cwd=root))
    return {x['tag']: {k: v for k, v in x.items() if k != 'tag'} for x in items}


def definition_index(raw, context):
    decls = {d['name']: d for d in raw['declarations']}
    entries = []
    for name, d in sorted(decls.items()):
        if not d['public'] or d['kind'] == 'theorem':
            continue
        entries.append({'name': name, 'kind': d['kind'], 'module': d['module'],
                        'file': d['module'].replace('.', '/') + '.lean', 'line': d['line'],
                        'type': d['display_type'],
                        'fingerprint': fingerprint(['const', name,
                            [['param', i] for i in range(d['universes'])]], decls, context)})
    return {'schema': 'perclib-definitions-v1', 'context': context, 'definitions': entries}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('raw', type=Path)
    parser.add_argument('--definitions-output', type=Path)
    parser.add_argument('--output', type=Path, default=Path('manifest.json'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    context = {'lean': (root / 'lean-toolchain').read_text().strip(),
               'dependencies': json.loads((root / 'lake-manifest.json').read_text())['packages']}
    # Paths/config are build metadata, not mathematical fingerprint inputs.
    context['dependencies'] = sorted([{'name': p['name'], 'rev': p['rev']} for p in context['dependencies']], key=lambda p: p['name'])
    result = build(json.loads(args.raw.read_text()), catalog_from(root), context)
    result['commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    result['ci_run'] = __import__('os').environ.get('MANIFEST_CI_RUN')
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
    if args.definitions_output:
        index = definition_index(json.loads(args.raw.read_text()), context)
        index.update(commit=result['commit'], ci_run=result['ci_run'])
        args.definitions_output.write_text(json.dumps(index, indent=2, ensure_ascii=False) + '\n')


if __name__ == '__main__':
    main()
