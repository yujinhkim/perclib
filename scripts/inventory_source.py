#!/usr/bin/env python3
"""Reproducible mechanical screening, explicitly not a semantic claim census."""
from __future__ import annotations
import argparse
import bisect
import collections
import csv
import hashlib
import json
import os
import pathlib
import re

parser = argparse.ArgumentParser(
    description='Mechanically screen a LaTeX mathematical source; not a semantic claim census.')
parser.add_argument('--source', required=True, type=pathlib.Path,
                    help='Input LaTeX source (relative to the working directory).')
parser.add_argument('--output-dir', required=True, type=pathlib.Path,
                    help='Directory for generated JSON and TSV inventories.')
args = parser.parse_args()
SOURCE = args.source
OUT = args.output_dir
OUT.mkdir(parents=True, exist_ok=True)
SOURCE_LABEL = pathlib.Path(os.path.relpath(SOURCE, pathlib.Path.cwd())).as_posix()
with SOURCE.open(encoding='utf-8', newline='') as source_file:
    raw = source_file.read()

def strip_comments(text):
    result = []
    for line in text.splitlines(keepends=True):
        cut = len(line)
        for i, c in enumerate(line):
            if c == '%':
                j = i - 1
                while j >= 0 and line[j] == '\\':
                    j -= 1
                if (i - 1 - j) % 2 == 0:
                    cut = i
                    break
        result.append(line[:cut] + ''.join('\n' if c == '\n' else ' ' for c in line[cut:]))
    return ''.join(result)

src = strip_comments(raw)
line_starts = [0] + [m.end() for m in re.finditer('\n', src)]
def line(offset):
    return bisect.bisect_right(line_starts, offset)

def balanced(offset, opening='{', closing='}'):
    """Read one balanced argument; escaped delimiters do not change depth."""
    while offset < len(src) and src[offset].isspace():
        offset += 1
    if offset >= len(src) or src[offset] != opening:
        return None, offset
    start = offset + 1
    depth = 1
    i = start
    while i < len(src):
        if src[i] == '\\':
            i += 2
            continue
        if src[i] == opening:
            depth += 1
        elif src[i] == closing:
            depth -= 1
            if depth == 0:
                return src[start:i], i + 1
        i += 1
    raise ValueError(f'Unclosed argument at line {line(offset)}')

headings = []
chapter_number = 0
current = {'chapter_number': None, 'chapter_title': None, 'section_title': None}
for m in re.finditer(r'\\(part|chapter|section|subsection|subsubsection)(\*)?', src):
    kind, star = m.group(1), bool(m.group(2))
    offset = m.end()
    _, after_optional = balanced(offset, '[', ']')
    title, end = balanced(after_optional)
    if title is None:
        continue
    if kind == 'chapter':
        if not star:
            chapter_number += 1
        current = {'chapter_number': None if star else chapter_number,
                   'chapter_title': title, 'section_title': None}
    elif kind == 'section':
        current['section_title'] = title
    headings.append({'kind': kind, 'starred': star, 'line': line(m.start()),
                     'offset': m.start(), 'end_offset': end, 'title': title, **current})

heading_offsets = [h['offset'] for h in headings]
def context(offset):
    i = bisect.bisect_right(heading_offsets, offset) - 1
    h = headings[i] if i >= 0 else {}
    return {k: h.get(k) for k in ['chapter_number', 'chapter_title', 'section_title']}

declared = []
for m in re.finditer(r'\\newtheorem(\*)?\s*\{([^{}]+)\}', src):
    declared.append({'environment': m.group(2), 'unnumbered': bool(m.group(1)), 'line': line(m.start())})
theorem_names = {d['environment'] for d in declared}
all_environments = []
stack = []
for m in re.finditer(r'\\(begin|end)\s*\{([^{}]+)\}', src):
    op, env = m.groups()
    if op == 'begin':
        title, title_end = balanced(m.end(), '[', ']')
        stack.append({'environment': env, 'start_offset': m.start(),
                      'content_offset': title_end, 'start_line': line(m.start()),
                      'title': title, 'parent_environment': stack[-1]['environment'] if stack else None,
                      'ancestor_environments': [s['environment'] for s in stack]})
    else:
        if not stack or stack[-1]['environment'] != env:
            raise ValueError(f'Environment mismatch {env!r} at line {line(m.start())}')
        record = stack.pop()
        record.update(end_offset=m.end(), end_line=line(m.end()-1), **context(record['start_offset']))
        text = src[record['content_offset']:m.start()].strip()
        record['labels'] = re.findall(r'\\label\s*\{([^{}]+)\}', text)
        record['text'] = text
        all_environments.append(record)
if stack:
    raise ValueError('Unclosed environments')
all_environments.sort(key=lambda r: r['start_offset'])
statements = [r for r in all_environments if r['environment'] in theorem_names]
proofs = [r for r in all_environments if r['environment'] in {'proof', 'proof*'}]

math_env_names = {'equation', 'equation*', 'align', 'align*', 'alignat', 'alignat*',
                  'gather', 'gather*', 'multline', 'multline*', 'displaymath', 'eqnarray', 'eqnarray*'}
inner_math_names = {'aligned', 'alignedat', 'split', 'cases', 'gathered', 'matrix', 'pmatrix', 'bmatrix', 'smallmatrix'}
displays = []
for r in all_environments:
    if r['environment'] in math_env_names and not any(e in math_env_names for e in r['ancestor_environments']):
        displays.append({'kind': r['environment'], 'start_offset': r['start_offset'],
                         'end_offset': r['end_offset'], 'start_line': r['start_line'],
                         'end_line': r['end_line'], **context(r['start_offset'])})
for pattern, kind in [(r'\\\[([\s\S]*?)\\\]', '\\[...\\]'), (r'(?<!\\)\$\$([\s\S]*?)(?<!\\)\$\$', '$$...$$')]:
    for m in re.finditer(pattern, src):
        displays.append({'kind': kind, 'start_offset': m.start(), 'end_offset': m.end(),
                         'start_line': line(m.start()), 'end_line': line(m.end()-1), **context(m.start())})
displays.sort(key=lambda r: r['start_offset'])
# Exclude any recognized display enclosed in another recognized display.
displays = [r for i, r in enumerate(displays) if not any(
    p['start_offset'] <= r['start_offset'] and r['end_offset'] <= p['end_offset']
    for p in displays[:i])]

assertion_pattern = re.compile(r'\b(?:we have|one has|we obtain|it follows|implies|there (?:is|are|exists)|'
 r'for (?:every|all|each)|satisf(?:y|ies)|equals?|bounded|finite|infinite|continuous|analytic|'
 r'converges?|convergence|inequality|identity|estimate|upper bound|lower bound|probability|'
 r'independent|equivalent|almost surely|if and only if|is known|can be shown|follows from|'
 r'is given by|are given by|can be defined|is defined|we define|define|denote|let)\b', re.I)
tag_patterns = {
 'heuristic_or_expectation_language': r'\b(?:heuristic|schematic|informal|expected|expectation is that|predict|prediction|should|conjectur|ansatz)\w*\b|\\approx',
 'quoted_or_external_input_language': r'\b(?:quoted|known|standard input|standard theorem|classical theorem|external input|we will use|we use the following)\b',
 'conditional_language': r'\b(?:if|assum(?:e|es|ing|ption)|provided|under the|conditional|whenever)\b',
 'definition_language': r'\b(?:define|defined|definition|denote|write|let|called|say that)\b',
 'proof_language': r'\b(?:proof|prove|by BK|by Harris|by Russo|summing|integrating|differentiating|hence|therefore|it follows)\b',
}
candidates = []
for m in re.finditer(r'\S[\s\S]*?(?=\n[ \t]*\n|\Z)', src):
    start, end = m.start(), m.end()
    paragraph = m.group().strip()
    if start < src.find('\\begin{document}'):
        continue
    matching_displays = [d for d in displays if start < d['end_offset'] and d['start_offset'] < end]
    has_inline = bool(re.search(r'(?<!\\)\$(?!\$)|\\\(', paragraph))
    language_match = bool(assertion_pattern.search(paragraph))
    if not matching_displays and not language_match:
        continue
    enclosing_statements = [i+1 for i, s in enumerate(statements) if start < s['end_offset'] and s['start_offset'] < end]
    enclosing_proofs = [i+1 for i, p in enumerate(proofs) if start < p['end_offset'] and p['start_offset'] < end]
    candidates.append({'candidate_id': f'P{len(candidates)+1:04d}',
       'start_line': line(start), 'end_line': line(end-1), **context(start),
       'display_count_overlapping': len(matching_displays), 'contains_inline_math': has_inline,
       'assertion_language_match': language_match,
       'overlapping_named_statement_ids': enclosing_statements,
       'overlapping_proof_ids': enclosing_proofs,
       'tags': [tag for tag, pat in tag_patterns.items() if re.search(pat, paragraph, re.I)],
       'text': paragraph})

for i, s in enumerate(statements, 1):
    s['statement_id'] = f'S{i:03d}'
    s['tags'] = [tag for tag, pat in tag_patterns.items() if re.search(pat, (s['title'] or '') + '\n' + s['text'], re.I)]

def counts(records, key):
    return dict(sorted(collections.Counter(str(r.get(key)) for r in records).items()))

summary = {
 'inventory_kind': 'mechanical_screening_not_semantic_claim_census',
 'identifier_policy': 'Snnn and Pnnnn identifiers are provisional mechanical IDs for this source snapshot, not canonical mathematical assertion IDs.',
 'source_path': SOURCE_LABEL, 'source_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
 'bytes': SOURCE.stat().st_size, 'physical_lines_splitlines': len(raw.splitlines()),
 'newline_characters': raw.count('\n'),
 'headings_total': len(headings), 'headings_by_kind': counts(headings, 'kind'),
 'numbered_chapters': chapter_number,
 'theorem_environments_declared': declared,
 'named_statement_environments_total': len(statements),
 'named_statement_environments_by_kind': counts(statements, 'environment'),
 'named_statement_environments_with_label': sum(bool(r['labels']) for r in statements),
 'explicit_proof_environments': len(proofs),
 'outer_display_math_blocks': len(displays), 'display_blocks_by_kind': counts(displays, 'kind'),
 'nested_math_environments_by_kind': counts([r for r in all_environments if r['environment'] in inner_math_names], 'environment'),
 'all_labels_total': len(re.findall(r'\\label\s*\{([^{}]+)\}', src)),
 'mechanical_candidate_paragraphs': len(candidates),
 'candidate_paragraphs_with_display': sum(c['display_count_overlapping'] > 0 for c in candidates),
 'candidate_paragraphs_without_display': sum(c['display_count_overlapping'] == 0 for c in candidates),
 'candidate_paragraphs_overlapping_named_statement': sum(bool(c['overlapping_named_statement_ids']) for c in candidates),
 'candidate_paragraphs_overlapping_explicit_proof': sum(bool(c['overlapping_proof_ids']) for c in candidates),
 'candidate_paragraphs_with_neither_named_statement_nor_explicit_proof': sum(not c['overlapping_named_statement_ids'] and not c['overlapping_proof_ids'] for c in candidates),
 'candidate_paragraph_tags': dict(collections.Counter(t for c in candidates for t in c['tags'])),
 'chapter_counts': []
}
for h in [h for h in headings if h['kind'] == 'chapter']:
    chap = h['chapter_title']
    summary['chapter_counts'].append({
      'chapter_number': h['chapter_number'], 'title': chap, 'start_line': h['line'],
      'sections': sum(r['kind'] == 'section' and r['chapter_title'] == chap for r in headings),
      'named_statements': sum(r['chapter_title'] == chap for r in statements),
      'proof_environments': sum(r['chapter_title'] == chap for r in proofs),
      'display_blocks': sum(r['chapter_title'] == chap for r in displays),
      'candidate_paragraphs': sum(r['chapter_title'] == chap for r in candidates),
    })

payload = {'identifier_policy': 'Snnn and Pnnnn identifiers are provisional mechanical IDs for this source snapshot, not canonical mathematical assertion IDs.', 'method': 'Mechanical LaTeX screening; not an exhaustive semantic claim inventory. Comments replaced by spaces preserving offsets. Balanced heading arguments. Named environments parsed from declared newtheorem names. Outer display math blocks counted once; inner aligned/split/cases not separate blocks. Candidate units are blank-line-delimited paragraphs containing a recognized display or a case-insensitive assertion/definition keyword; candidates may contain multiple claims or no mathematical assertion. Proof text is included and tagged. Macro expansion and semantic inference are not performed.',
 'summary': summary, 'headings': headings, 'named_statements': statements,
 'display_math_blocks': displays, 'candidate_paragraphs': candidates}
(OUT / 'inventory.json').write_text(json.dumps(payload, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def write_tsv(name, rows, fields):
    with (OUT / name).open('w', newline='', encoding='utf-8') as f:
        writer = csv.DictWriter(f, fieldnames=fields, delimiter='\t', lineterminator='\n', extrasaction='ignore')
        writer.writeheader()
        for r in rows:
            row = dict(r)
            for k, v in row.items():
                if isinstance(v, list):
                    row[k] = '; '.join(map(str, v))
            writer.writerow(row)
write_tsv('headings.tsv', headings,
 ['kind', 'starred', 'line', 'chapter_number', 'chapter_title', 'title'])
write_tsv('named_statements.tsv', statements,
 ['statement_id', 'environment', 'start_line', 'end_line', 'chapter_number', 'chapter_title', 'section_title', 'title', 'labels', 'tags'])
write_tsv('candidate_paragraphs.tsv', candidates,
 ['candidate_id', 'start_line', 'end_line', 'chapter_number', 'chapter_title', 'section_title', 'display_count_overlapping', 'contains_inline_math', 'assertion_language_match', 'overlapping_named_statement_ids', 'overlapping_proof_ids', 'tags', 'text'])
(OUT / 'summary.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps(summary, ensure_ascii=False, indent=2))
