#!/usr/bin/env python3
"""Regression tests for the source-packet adapter; no topology is approved."""
import import_source_packets as importer
import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from proof_depgraph import parse_graph

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT.parents[1]
MANIFEST = "docs/orchestration/FROZEN_ANCHOR_MANIFEST.json"

BLOCK = """RECORD consumer
KIND definition
TITLE Test model
STATEMENT_SOURCE .scratch/source/paper.html#S1.SS2.p1@L45-L45
PROOF_SOURCE -
SOURCE_HYPOTHESES -
SOURCE_QUANTIFIERS -
SOURCE_CONCLUSION test statement
CONSTANT_SCOPE -
END

RECORD provider
KIND external
TITLE Test cited item
STATEMENT_SOURCE .scratch/source/paper.html#S1.SS2.p1@L49-L49
SOURCE_HYPOTHESES -
SOURCE_QUANTIFIERS -
SOURCE_CONCLUSION test citation
CONSTANT_SCOPE -
END

EDGE
FROM consumer
TO provider
TYPE hypothesis
USE_SITE .scratch/source/paper.html#S1.SS2.p1@L49-L49
USE_TEXT the cited fact is used here
TARGET_STATE present
END
"""


class PacketReaderTests(unittest.TestCase):
    def write(self, name, text):
        path = ROOT / ".scratch/importer-work" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def test_block_edge_end_is_flushed_to_owner(self):
        chunk = importer.chunks(self.write("block-fixture-test.md", BLOCK))
        self.assertEqual([item.identifier for item in chunk], ["consumer", "provider"])
        self.assertEqual(len(chunk[0].edges), 1)
        self.assertEqual(chunk[0].edges[0][0], "provider")
        self.assertIn("hypothesis", chunk[0].edges[0][2])
        self.assertIn("TARGET_STATE present", chunk[0].edges[0][3])

    def test_unknown_edge_owner_rejected(self):
        with self.assertRaises(importer.PacketError):
            importer.chunks(self.write("owner-mutation.md", BLOCK.replace("FROM consumer", "FROM other")))

    def test_unterminated_edge_rejected(self):
        with self.assertRaises(importer.PacketError):
            importer.chunks(self.write("unterminated-edge.md", BLOCK.rsplit("END", 1)[0]))

    def test_malformed_record_and_duplicate_edge_field_rejected(self):
        malformed = BLOCK.replace("STATEMENT_SOURCE", "STATEENT_SOURCE", 1)
        chunks = importer.chunks(self.write("unknown-field.md", malformed))
        self.assertIn("UNSCHEMAED INPUT", chunks[0].notes[0])
        with self.assertRaises(importer.PacketError):
            importer.normalize(ROOT / ".scratch/importer-work/unknown-field.md", ROOT, MANIFEST)
        with self.assertRaises(importer.PacketError):
            importer.chunks(self.write("duplicate-edge-field.md", BLOCK.replace("TO provider", "TO provider\nTO provider")))

    def test_complete_fixture_normalizes_with_html_span_not_canonical_line(self):
        text, stats = importer.normalize(self.write("normalization-fixture.md", BLOCK), ROOT, MANIFEST)
        self.assertEqual((stats["records"], stats["edges"]), (2, 1))
        graph = parse_graph(text, "<fixture>")
        self.assertFalse(graph.diagnostics.items)
        self.assertEqual(len(graph.nodes["consumer"].edges), 1)
        locator = graph.nodes["consumer"].value("STATEMENT_SOURCE")
        self.assertIn(".scratch/source/paper.html#S1.SS2.p1@L334-L", locator)
        self.assertNotIn("@L45-L45", locator)
        self.assertEqual((ROOT / ".scratch/source/paper.html").read_text().splitlines()[333].split(" ", 1)[0], "<div")

    def test_blank_and_truncated_mathematical_fields_fail(self):
        with self.assertRaisesRegex(importer.PacketError, "SOURCE_CONCLUSION"):
            importer.normalize(self.write("blank-conclusion.md", BLOCK.replace("test statement", "")), ROOT, MANIFEST)
        with self.assertRaisesRegex(importer.PacketError, "truncated SOURCE_CONCLUSION"):
            importer.normalize(self.write("truncated-conclusion.md", BLOCK.replace("test statement", "multiply the")), ROOT, MANIFEST)

    def test_declared_packet_edge_counts(self):
        cases = [
            ("smwo9ehml/m1/I1DEPGRAPH.md", 27, 56),
            ("smwo9ehml/m2/I23Nodes.md", 39, 37),
            ("smwo9ehml/m5/I54Packet.md", 87, 134),
            ("smwo9ehml/m5/I54DeferredRoots.md", 3, 23),
        ]
        for suffix, nodes, edges in cases:
            path = PROJECT / ".ultramath" / suffix
            if not path.is_file():
                self.skipTest(f"research packet is unavailable: {path}")
            with self.subTest(path=path.name):
                records = importer.chunks(path)
                self.assertEqual(len(records), nodes)
                self.assertEqual(sum(len(record.edges) for record in records), edges)

    def test_incomplete_i5_not_promoted(self):
        for suffix in ("smwo9ehml/m5/I54Packet.md", "smwo9ehml/m5/I54DeferredRoots.md"):
            path = PROJECT / ".ultramath" / suffix
            if not path.is_file():
                self.skipTest(f"research packet is unavailable: {path}")
            with self.subTest(path=path.name):
                with self.assertRaises(importer.PacketError):
                    importer.normalize(path, ROOT, MANIFEST)


    def test_table_and_source_layer_aliases(self):
        index = importer.SourceIndex(ROOT)
        table = index.span("S1.E1", 427)
        self.assertEqual(table.path, ".scratch/source/paper.html")
        self.assertEqual(table.first, 336)
        self.assertIn('id="S1.E1"', (ROOT / table.path).read_text().splitlines()[table.first - 1])
        canonical = index.resolve("P#S4.p3.1.1@L815-L831")
        self.assertEqual(
            (canonical.path, canonical.anchor, canonical.first, canonical.last),
            (".scratch/source/paper-tex.txt", "S4.p3.1.1", 815, 831),
        )
        html = index.resolve("HTML#S1.E1@L336-L336")
        self.assertEqual((html.path, html.first, html.last),
                         (".scratch/source/paper.html", 336, 336))
        inline = index.span("S4.p3.1.1", 815)
        self.assertEqual(inline.anchor, "S4.p3.1")
        with self.assertRaises(importer.PacketError):
            index.resolve("P#no.such.id@L815-L831")

    def test_compressed_scalar_fields_and_native_edge(self):
        packet = """### NODE consumer
NODE: consumer
KIND step | TITLE Test proof step
STATEMENT_SOURCE P#S4.p3.1.1@L815-L831 ; PROOF_SOURCE same block
CONTRACT_ID: test.consumer (v1)
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES source premise | SOURCE_QUANTIFIERS all r>0 | SOURCE_CONCLUSION source conclusion
CONSTANT_SCOPE no implicit constant
FROZEN_FILE - | FROZEN_DECL - | FROZEN_ANCHOR_ID - | FROZEN_ABI_SHA256 -
DEPS [] | ROUTES - | ROUTE_FOR -
PROPOSED extractor=m3 | reviewer - | TOPOLOGY_STATUS PROPOSED | LEAN_STATUS NOT_STARTED | LEAN_REF - | LEAN_NOTE -
EDGE: provider | P#S4.p3.2.1@L819-L821 | direct consumer use
NOTE compressed input is retained as research only

RECORD provider
KIND: external
TITLE: Test external leaf
STATEMENT_SOURCE: HTML#S1.E1@L336-L344
PROOF_SOURCE: none in this test
CONTRACT_ID: test.provider
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: external hypotheses
SOURCE_QUANTIFIERS: fixed test instance
SOURCE_CONCLUSION: external conclusion
CONSTANT_SCOPE: no implicit constant
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: m3
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
END
"""
        path = self.write("compressed-native.md", packet)
        chunks = importer.chunks(path)
        self.assertEqual((len(chunks), sum(len(c.edges) for c in chunks)), (2, 1))
        text, stats = importer.normalize(path, ROOT, MANIFEST)
        self.assertEqual((stats["records"], stats["edges"]), (2, 1))
        graph = parse_graph(text, "<compressed-native>")
        self.assertFalse(graph.diagnostics.items)
        self.assertEqual(graph.nodes["consumer"].value("CONTRACT_ID"), "test.consumer")
        self.assertEqual(graph.nodes["consumer"].value("STATEMENT_SOURCE"),
                         ".scratch/source/paper-tex.txt#S4.p3.1.1@L815-L831")
        import proof_depgraph as native
        native._validate_node_shape(graph, ROOT, set())
        native._validate_topology(graph, graph.nodes, [], [], [])
        self.assertFalse(graph.diagnostics.items)
        self.assertEqual(graph.nodes["consumer"].deps, ["provider"])
        self.assertIn("extractor=m3", graph.nodes["consumer"].value("NOTE"))

    def test_annotated_routes_and_repeated_notes_are_preserved(self):
        packet = BLOCK.replace(
            "DEPS: -", "DEPS: -", 1
        ).replace(
            "RECORD provider", "RECORD provider", 1
        ).replace(
            "NOTE", "NOTE", 1
        )
        packet += "\nRECORD routes\nKIND route\nTITLE route life\nSTATEMENT_SOURCE P#S4.p3.1.1@L815-L831\nPROOF_SOURCE same\nSOURCE_HYPOTHESES test\nSOURCE_QUANTIFIERS -\nSOURCE_CONCLUSION test\nCONSTANT_SCOPE test\nROUTES: R.1 | R.2 (DISJUNCTION: at least one holds; never conjoined)\nNOTE first note\nNOTE second note\nEND\n"
        chunks = importer.chunks(self.write("annotated-routes.md", packet))
        record = next(c for c in chunks if c.identifier == "routes")
        self.assertEqual(importer._identifier_list(record.fields["ROUTES"], "ROUTES", "routes"), ["R.1", "R.2"])
        self.assertIn("DISJUNCTION", " ".join(record.notes))
        self.assertIn("first note second note", record.fields["NOTE"])

    def test_latest_i23_native_shape_and_topology_gate(self):
        path = PROJECT / ".ultramath/smwobyis9/m2/I23Packet.m2.md"
        if not path.is_file():
            self.skipTest(f"research packet is unavailable: {path}")
        text, stats = importer.normalize(path, ROOT, MANIFEST)
        self.assertEqual((stats["records"], stats["edges"]), (68, 93))
        graph = parse_graph(text, str(path))
        roots = [x for x in graph.metadata.get("ROOTS", "-").split(",") if x != "-"]
        assumptions = [x for x in graph.metadata.get("STANDING_ASSUMPTIONS", "-").split(",") if x != "-"]
        frozen = [x for x in graph.metadata.get("FROZEN_ANCHORS", "-").split(",") if x != "-"]
        import proof_depgraph as native
        native._validate_node_shape(graph, ROOT, set(frozen))
        nodes = native._apply_amendments(graph, ROOT, set(frozen))
        native._validate_topology(graph, nodes, roots, assumptions, frozen)
        self.assertFalse(graph.diagnostics.items)


if __name__ == "__main__":
    unittest.main()
