#!/usr/bin/env python3
"""Fail-closed checks for the pinned arXiv HTML restitution.

The caller must explicitly update the pinned paper and trusted output hashes in a
reviewed source revision. This file does not infer approval or generate a new
baseline. Converter bugs and source-file errors are not coverage results.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
from pathlib import Path
import sys

from html_restitution import convert

HTML_SHA256 = "246ccda2bfadabc8f6ce1670f015ddcb58b99f896ea16ff722321532f074d76f"
TEXT_SHA256 = "7658da0615631fa69f53a9a7d7b6de2526e83016ad4ecd5c0159774a8d071755"
MATH_COUNT = 2838
INEQUALITY_MATH_COUNT = 287
REQUIRED_IDS = {
    "S1.Thmthm3.2", "S1.Thmthm6.2", "S1.Thmthm14.2", "S1.Thmthm15.2", "S4.Thmthm18.2",
}
PROBES = ("localStorage", "initializeReadingPreferences", "<script", "<style", "document.", "window.matchMedia")
TAGS = r"a|b|i|p|br|div|span|em|sup|sub|ul|ol|li|td|tr|table|tbody|img|href|math|mrow|mi|mo|mn|msup|msub|section|nav|head|body|html|script|style|figure|figcaption|annotation|semantics"


def math_errors(text: str, maths: list[str]) -> list[str]:
    missing = [m for m in maths if f"${m}$" not in text]
    return [f"missing or altered math annotations: {len(missing)}"] if missing else []


def restitution_errors(root: Path, html_file: Path, text_file: Path, locators: Path) -> list[str]:
    failures: list[str] = []
    for file in (html_file, text_file, locators):
        if not file.is_file():
            failures.append(f"missing file: {file}")
    if failures:
        return failures
    html_bytes, text_bytes = html_file.read_bytes(), text_file.read_bytes()
    if hashlib.sha256(html_bytes).hexdigest() != HTML_SHA256:
        failures.append("HTML digest is not the pinned arXiv-v1 snapshot")
    if hashlib.sha256(text_bytes).hexdigest() != TEXT_SHA256:
        failures.append("restituted text digest is not the reviewed lossless candidate")
    if failures:
        return failures
    text, _, maths = convert(str(html_file))
    if text != text_bytes.decode("utf-8"):
        failures.append("converter output differs from the pinned lossless text")
    failures.extend(math_errors(text, maths))
    if len(maths) != MATH_COUNT:
        failures.append(f"expected {MATH_COUNT} math annotations, got {len(maths)}")
    inequalities = [m for m in maths if "<" in m or ">" in m]
    if len(inequalities) != INEQUALITY_MATH_COUNT:
        failures.append(f"expected {INEQUALITY_MATH_COUNT} inequality annotations, got {len(inequalities)}")
    for probe in PROBES:
        if probe in text:
            failures.append(f"script/chrome leak: {probe}")
    if text.count("I.1.1 Critical phenomena in long-range percolation") != 1:
        failures.append("TOC/front-matter section-header duplication")
    import re
    residual = re.findall(r"</?(?:" + TAGS + r")(?:\s[^<>\n]{0,40})?/?>", text)
    if residual:
        failures.append(f"residual tag-like strings: {residual[:3]}")
    try:
        with locators.open(encoding="utf-8", newline="") as stream:
            rows = list(csv.DictReader(stream, delimiter="\t"))
    except (OSError, csv.Error) as error:
        return failures + [f"cannot read locators: {error}"]
    if not rows or list(rows[0]) != ["line", "html_id", "locator"]:
        failures.append("unexpected locator schema")
        return failures
    segments = text.split("\n\n")
    if len(rows) != len(segments):
        failures.append(f"locator count {len(rows)} does not match output segments {len(segments)}")
    for row in rows:
        try:
            int(row["line"])
        except (TypeError, ValueError):
            failures.append(f"invalid locator line: {row}")
            continue
        html_id = row["html_id"]
        if html_id and row["locator"] != "paper.html#" + html_id:
            failures.append(f"locator/ID mismatch: {row}")
    missing_ids = REQUIRED_IDS.difference(row["html_id"] for row in rows)
    if missing_ids:
        failures.append(f"required source IDs missing: {sorted(missing_ids)}")
    return failures


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    args = parser.parse_args(argv)
    root = args.root
    failures = restitution_errors(
        root,
        root / ".scratch/source/paper.html",
        root / ".scratch/source/paper-tex.txt",
        root / ".scratch/source/paper-tex.locators.tsv",
    )
    if failures:
        print("SOURCE-RESTITUTION GUARD FAILED:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1
    print(f"SOURCE-RESTITUTION GUARD OK: {MATH_COUNT} math annotations, "
          f"{INEQUALITY_MATH_COUNT} inequality annotations, pinned hashes and locator schema verified")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
