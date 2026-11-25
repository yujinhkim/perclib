#!/usr/bin/env python3
"""Inventory numbered mathematical environments in the pinned arXiv HTML.

This reports source metadata only: no proof-status or formalization-status inference.
"""
import argparse
import csv
from collections import Counter
from pathlib import Path
import re

LABEL = re.compile(r'((?:Theorem|Remark|Definition|Lemma|Proposition|Corollary)\s+(I\.[0-9.]+))')
ENV = re.compile(
    r'<div id="(?P<htmlid>S[1-5]\.Thmthm(?P<number>[0-9]+))" '
    r'class="ltx_theorem ltx_theorem_(?P<kind>[^"]+)"', re.S)


def inventories(html: str):
    for match in ENV.finditer(html):
        snippet = html[match.start():match.start() + 3000]
        label = LABEL.search(snippet)
        yield {
            'html_id': match.group('htmlid'),
            'source_id': label.group(1) if label else f'numbered-environment-{match.group("number")}',
            'kind': match.group('kind'),
            'html_line': match.start() and html.count('\n', 0, match.start()) + 1,
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('html')
    parser.add_argument('output')
    args = parser.parse_args()
    rows = list(inventories(Path(args.html).read_text(encoding='utf-8')))
    with Path(args.output).open('w', newline='', encoding='utf-8') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), delimiter='\t')
        writer.writeheader()
        writer.writerows(rows)
    print(f'Wrote {len(rows)} numbered source environments to {args.output}')
    print('By section:', dict(Counter(row['source_id'].split('.')[1] for row in rows)))
    print('By kind:', dict(Counter(row['kind'] for row in rows)))


if __name__ == '__main__':
    main()
