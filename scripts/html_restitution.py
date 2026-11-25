#!/usr/bin/env python3
"""Lossless replacement for .scratch/.../source/html2tex.py.

Why: the incumbent converter restores math alttext first and then runs the
generic tag-strip regex `<[^>]+>` over the whole document.  Any unescaped '<'
inside restored LaTeX (`r<\\infty`, `d=3\\alpha<6`, `\\beta_c<\\infty`) starts a
fake "tag" that the strip then removes up to the next '>', deleting source text.
It also keeps <script>, <style>, <head> and the TOC <nav> content.

Fix: a single html.parser.HTMLParser pass.  Math elements are replaced by an
opaque token at the moment their start tag is seen (the parser hands over the
alttext attribute intact, so '<' and '>' cannot be confused with markup); the
MathML body is skipped.  Tables of tokens are substituted back only after all
tag stripping and whitespace normalisation is finished, so restored LaTeX is
never re-interpreted as markup.  script/style/head/nav are skipped.

Locators: every emitted line is mapped to the innermost HTML id open when the
line began, giving `paper.html#S1.Thmthm6`-style anchors in a sidecar TSV; with
--inline-locators the same token is prepended to the line.

Usage:
  python3 html2tex_v2.py paper.html paper-tex.txt [--locators out.tsv]
                          [--inline-locators] [--self-check]
"""
import argparse
import html.parser
import re
import sys

BLOCK = {"p", "div", "h1", "h2", "h3", "h4", "h5", "h6", "li", "tr", "table",
         "section", "blockquote", "figure", "figcaption", "dl", "dt", "dd"}
SKIP = {"script", "style", "head", "nav", "header", "footer", "dialog"}
# arXiv/ar5iv chrome containers that hold no source text
CHROME_ID = {"header", "footer"}
CHROME_CLASS = {"arxiv-header", "ltx_page_navbar", "ltx_page_logo"}


class Lossless(html.parser.HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.chunks = []          # list of str, tokens included
        self.math = []            # alttexts in order
        self.stack = []           # (tag, id)
        self.skip = 0
        self.mathdepth = 0
        self.line_id = []         # id recorded at the start of each line
        self.pending_id = None
        self.cur = []

    # -- helpers -------------------------------------------------------
    def _id(self):
        for tag, i in reversed(self.stack):
            if i:
                return i
        return ""

    def _emit(self, s):
        if not s or self.skip or self.mathdepth:
            return
        if not "".join(self.cur).strip() and s.strip():
            self.pending_id = self._id()
        self.cur.append(s)

    def _newline(self):
        line = "".join(self.cur)
        self.chunks.append(line)
        self.line_id.append(self.pending_id or "")
        self.cur = []
        self.pending_id = None

    # -- parser callbacks ---------------------------------------------
    def handle_starttag(self, tag, attrs):
        if tag in SKIP:
            self.skip += 1
            return
        if self.skip:
            return
        d = dict(attrs)
        if (d.get("id") in CHROME_ID
                or set((d.get("class") or "").split()) & CHROME_CLASS):
            self.skip += 1
            self.stack.append(("__chrome__", None))
            return
        if tag == "math":
            if self.mathdepth == 0:
                a = d.get("alttext")
                if a is not None:
                    self.math.append(a)
                    # emit BEFORE raising mathdepth, else _emit suppresses it
                    self._emit("\x00M%d\x00" % (len(self.math) - 1))
            self.mathdepth += 1
            return
        if tag == "br":
            self._newline()
            return
        self.stack.append((tag, d.get("id")))

    def handle_startendtag(self, tag, attrs):
        if tag in SKIP or self.skip:
            return
        if tag == "br":
            self._newline()

    def handle_endtag(self, tag):
        if tag in SKIP:
            self.skip = max(0, self.skip - 1)
            return
        if self.skip:
            if self.stack and self.stack[-1][0] == "__chrome__":
                self.stack.pop()
            return
        if tag == "math":
            self.mathdepth = max(0, self.mathdepth - 1)
            return
        for i in range(len(self.stack) - 1, -1, -1):
            if self.stack[i][0] == tag:
                del self.stack[i:]
                break
        if tag in BLOCK:
            self._newline()
        elif tag == "math" or tag == "span":
            pass

    def handle_data(self, data):
        if self.skip or self.mathdepth:
            return
        self._emit(data)

    def close(self):
        super().close()
        if "".join(self.cur).strip():
            self._newline()


CHROME_LINES = {"Skip to main content", "Report Issue", "Back to Abstract",
                "Download PDF", "Contents", "Reading mode", "Colour theme",
                "Why HTML?", "Report GitHub Issue", "Submit without GitHub",
                "Submit in GitHub", "Description:", "Title:"}


def convert(src, inline=False):
    with open(src, encoding="utf-8") as stream:
        raw = stream.read()
    p = Lossless()
    p.feed(raw)
    p.close()
    lines, ids = [], []
    for line, lid in zip(p.chunks, p.line_id):
        # canonical post-processing: collapse spaces, drop pure-blank runs later
        t = re.sub(r"[ \t\r\f\v]+", " ", line)
        t = re.sub(r"\s+", " ", t).strip()
        if not t or t in CHROME_LINES:
            continue
        ids.append(lid)
        lines.append(t)
    out = []
    for t in lines:
        t = re.sub(r"\x00M(\d+)\x00",
                   lambda m: " $" + p.math[int(m.group(1))] + "$ ", t)
        out.append(t)
    if inline:
        out = [("[paper.html#%s] " % i if i else "") + t for i, t in zip(ids, out)]
    text = "\n\n".join(out) + "\n"       # one blank line between blocks, as canonical
    return text, ids, p.math


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("html")
    ap.add_argument("out")
    ap.add_argument("--locators")
    ap.add_argument("--inline-locators", action="store_true")
    ap.add_argument("--self-check", action="store_true")
    a = ap.parse_args()
    text, ids, maths = convert(a.html, a.inline_locators)
    open(a.out, "w", encoding="utf-8").write(text)
    print("wrote %s: %d lines, %d bytes, %d math elements"
          % (a.out, text.count("\n"), len(text.encode()), len(maths)))
    if a.locators:
        with open(a.locators, "w", encoding="utf-8") as f:
            f.write("line\thtml_id\tlocator\n")
            for n, i in enumerate(ids):
                f.write("%d\t%s\t%s\n" % (2 * n + 1, i,
                                             ("paper.html#" + i) if i else ""))
        print("wrote %s" % a.locators)
    if a.self_check:
        bad = [m for m in maths if ("$" + m + "$") not in text]
        print("math alttext present verbatim: %d/%d" % (len(maths) - len(bad), len(maths)))
        lt = [m for m in maths if "<" in m or ">" in m]
        ltbad = [m for m in lt if ("$" + m + "$") not in text]
        print("alttexts containing '<' or '>': %d, missing after conversion: %d"
              % (len(lt), len(ltbad)))
        for m in ltbad[:5]:
            print("   MISSING:", m)
        for probe in ("localStorage", "initializeReadingPreferences", "<script",
                      "<style", "document.", "window.matchMedia"):
            print("leak %-32s %s" % (probe, probe in text))
        toc = text.count("I.1.1 Critical phenomena in long-range percolation")
        print("occurrences of section I.1.1 head (TOC excluded if 1):", toc)
        HTMLTAGS = "a|b|i|p|br|div|span|em|sup|sub|ul|ol|li|td|tr|table|tbody|img|href|math|mrow|mi|mo|mn|msup|msub|section|nav|head|body|html|script|style|figure|figcaption|annotation|semantics"
        stray = re.findall(r"</?(?:%s)(?:\s[^<>\n]{0,40})?/?>" % HTMLTAGS, text)
        print("residual tag-like strings:", len(stray), stray[:3])
    return 0


if __name__ == "__main__":
    sys.exit(main())
