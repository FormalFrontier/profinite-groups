#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Data-only corruption and source-only replay tests for the pinned native adapter.

Formal Frontier Agents adapted the data-only controls through finite-group
Tate cohomology, polynomial-root-stability and Anchor's ideal-completion
recipe. These tests cannot replace the external native records.
"""

import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import generate_api as api


ROOT = Path(__file__).resolve().parent.parent
PARSER = argparse.ArgumentParser(description=__doc__)
PARSER.add_argument("--native-data", type=Path, required=True)


class NativeControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = {path: (ROOT / path).read_bytes() for path in api.SOURCE_INPUT_SHA256}
        cls.original = {
            module: (ARGS.native_data / ("declaration-data-" + module + ".bmp")).read_bytes()
            for module in api.MODULES
        }
        cls.records = {module: json.loads(raw) for module, raw in cls.original.items()}
        api.check_snapshot(api.SOURCE, cls.sources)
        api.validate(cls.records, cls.original, cls.sources, api.SOURCE)

    def corrupt(self, modify, diagnostic):
        records = copy.deepcopy(self.records)
        sources = dict(self.sources)
        modify(records, sources)
        raw = {module: json.dumps(record, ensure_ascii=False, sort_keys=True,
                                  separators=(",", ":")).encode("utf-8")
               for module, record in records.items()}
        with self.assertRaisesRegex(ValueError, diagnostic):
            api.render(records, raw, sources, api.SOURCE)

    def command(self, archive, native, check=True, python=sys.executable):
        args = [python, "-I", "-B", str(archive / "scripts/generate_api.py"),
                "--native-data", str(native), "--source-revision", api.SOURCE,
                "--docgen-revision", api.TOOL]
        if check:
            args.append("--check")
        return subprocess.run(args, cwd=archive, env={"PATH": "/no-git-binary"},
                              capture_output=True, text=True, check=False)

    def archive(self, base):
        archive = base / "source-only"
        (archive / "scripts").mkdir(parents=True)
        (archive / "docs").mkdir()
        for path, raw in self.sources.items():
            target = archive / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(raw)
        for path in ("scripts/generate_api.py", "scripts/test_generate_api.py",
                     "docs/README.md", "docs/Mathematics.md", "docs/API.md",
                     "docs/api-manifest.json"):
            (archive / path).write_bytes((ROOT / path).read_bytes())
        native = base / "external-native"
        native.mkdir()
        for module, raw in self.original.items():
            (native / ("declaration-data-" + module + ".bmp")).write_bytes(raw)
        return archive, native

    def test_unmodified_native_and_manifest(self):
        markdown, raw = api.render(self.records, self.original, self.sources, api.SOURCE)
        manifest = json.loads(raw)
        self.assertEqual(len(manifest["production_declarations"]), 502)
        self.assertEqual(len(manifest["public_client_declarations"]), 146)
        self.assertEqual(len(manifest["instance_table"]), 16)
        self.assertEqual(manifest["undocumented_count"], 132)
        self.assertEqual(markdown.count(b"\n#### "), 648 + 6)
        self.assertEqual(manifest["native_record_sha256"], api.NATIVE_RECORD_SHA256)
        self.assertEqual(manifest["inputs"], api.SOURCE_INPUT_SHA256)
        self.assertEqual(manifest["api_sha256"], api.digest(markdown))
        self.assertEqual((ROOT / "docs/API.md").read_bytes(), markdown)
        self.assertEqual((ROOT / "docs/api-manifest.json").read_bytes(), raw)
        self.assertNotIn(b"example.invalid", markdown + raw)
        self.assertNotIn(b"forgejo.vpn", markdown + raw)
        self.assertFalse(manifest["proof_certification"] or manifest["release_acceptance"])

    def test_missing_duplicate_kind_name_module_source_and_instances(self):
        module = "ProfiniteGroups.FiniteQuotientHom"
        rows = self.records[module]["declarations"]
        name = rows[0]["info"]["name"]
        controls = [
            ("missing/extra native declaration", lambda r, s: r[module]["declarations"].pop()),
            ("missing/extra native declaration", lambda r, s: r[module]["declarations"].append(
                copy.deepcopy(rows[0]))),
            ("duplicate native declaration", lambda r, s: r[module]["declarations"].__setitem__(
                1, copy.deepcopy(rows[0]))),
            ("native module name differs", lambda r, s: r[module].__setitem__("name", "Other")),
            ("wrong native name/kind", lambda r, s: r[module]["declarations"][0]["info"].__setitem__(
                "kind", "axiom")),
            ("wrong native name/kind", lambda r, s: r[module]["declarations"][0]["info"].__setitem__(
                "name", "unsupported name")),
            ("native source module/revision/path differs", lambda r, s: r[module]["declarations"][0]["info"].__setitem__(
                "sourceLink", "https://example.invalid/commit/main/Other.lean")),
            ("native self link differs", lambda r, s: r[module]["declarations"][0]["info"].__setitem__(
                "docLink", "./other.html#name")),
            ("missing/extra/wrong native instance table", lambda r, s: r[module]["instances"].pop()),
            ("duplicate native instance row", lambda r, s: r[module]["instances"].append(
                copy.deepcopy(r[module]["instances"][0]))),
            ("missing/extra/wrong native instance table", lambda r, s: r[module]["instances"][0].__setitem__(
                "className", "Other")),
            ("missing/extra/wrong native instance table", lambda r, s: r[module]["instances"][0].__setitem__(
                "typeNames", ["Other"])),
            ("invalid native source line", lambda r, s: r[module]["declarations"][0]["info"].__setitem__(
                "line", 0)),
            ("native raw record differs", lambda r, s: r[module]["imports"].append("Changed.Import")),
        ]
        self.assertIsInstance(name, str)
        for diagnostic, change in controls:
            with self.subTest(diagnostic=diagnostic):
                self.corrupt(change, diagnostic)
        self.corrupt(lambda r, s: r["ProfiniteGroups.FreeProduct"]["declarations"].__setitem__(
            0, copy.deepcopy(r["ProfiniteGroups.FreeProduct"]["declarations"][1])),
            "duplicate native declaration")

    def test_mixed_kinds_and_implicit_binders(self):
        module = "ProfiniteGroups.FreeProduct"
        for kind in ("structure", "ctor", "instance"):
            with self.subTest(kind=kind):
                self.corrupt(lambda records, sources: next(row for row in records[module]["declarations"]
                           if row["info"]["kind"] == kind)["info"].__setitem__("kind", "theorem"),
                           "native signature identity/format differs|instance table kind mismatch|native docstring missing")
        controls = [
            ("ProfiniteGroups.FiniteQuotientHom", "stageToContinuousHom_injective",
             "[TopologicalSpace F]", "TopologicalSpace", "OtherSpace"),
            ("ProfiniteGroups.FiniteQuotientHom", "stageToContinuousHom_injective",
             "(U : StageIndex G)", "StageIndex", "OtherIndex"),
            ("ProfiniteGroups.ProcyclicPower", "powerImage_index_dvd",
             "(hG : G.IsProcyclic)", "hG", "hK"),
            ("ProfiniteGroups.ProcyclicPower", "powerImage_index_dvd",
             "(hn : 0 < n)", "&lt;", "&le;"),
            ("ProfiniteGroups.ProcyclicInvariant",
             "isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq",
             "(H : ProfiniteGrp.{v})", "v}", "w}"),
        ]
        for module, short_name, binder, old, new in controls:
            with self.subTest(binder=binder):
                def remove_binder(records, sources):
                    row = next(row for row in records[module]["declarations"]
                               if row["info"]["name"].endswith(short_name))
                    self.assertIn(binder, api.Header(row["header"]).rendered())
                    self.assertIn(old, row["header"])
                    row["header"] = row["header"].replace(old, new,
                                                          2 if old == "StageIndex" else 1)
                    self.assertNotIn(binder, api.Header(row["header"]).rendered())
                self.corrupt(remove_binder, "missing signature binder")

    def test_active_html_docstrings_and_extra_file(self):
        module = "ProfiniteGroups.FiniteQuotientHom"
        for fragment in ("<script>alert(1)</script>", "<img src='x'>",
                         "<a href='javascript:evil'>x</a>", "<span onclick='evil'>x</span>",
                         "<div><span></div>", "<span id='bad' onclick='evil'>x</span>"):
            with self.subTest(fragment=fragment):
                self.corrupt(lambda r, s: r[module]["declarations"][0].__setitem__("header", fragment),
                             "native header|active/unknown")
        self.corrupt(lambda r, s: r[module]["declarations"][0]["info"].__setitem__(
            "doc", "<script>alert(1)</script>"), "active/unsupported native docstring")
        modified = dict(self.original)
        modified[module] += b" "
        with self.assertRaisesRegex(ValueError, "native raw record differs"):
            api.validate(self.records, modified, self.sources, api.SOURCE)
        with tempfile.TemporaryDirectory() as temporary:
            archive, native = self.archive(Path(temporary))
            (native / "unexpected.bmp").write_bytes(b"{}")
            result = self.command(archive, native)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("missing/extra native record file", result.stderr)

    def test_fixed_source_revision_tool_and_python_optimization(self):
        for path in self.sources:
            changed = dict(self.sources)
            changed[path] += b"\n"
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, "source/pin drift"):
                api.check_snapshot(api.SOURCE, changed)
        with self.assertRaisesRegex(ValueError, "source/pin inventory differs"):
            api.check_snapshot(api.SOURCE, {**self.sources, "extra.lean": b""})
        with self.assertRaisesRegex(ValueError, "unexpected/stale analyzed source revision"):
            api.check_snapshot("main", self.sources)
        with tempfile.TemporaryDirectory() as temporary:
            archive, native = self.archive(Path(temporary))
            targets = [(archive / "docs/API.md").read_bytes(),
                       (archive / "docs/api-manifest.json").read_bytes()]
            command = [sys.executable, "-O", str(archive / "scripts/generate_api.py"),
                       "--native-data", str(native), "--source-revision", api.SOURCE,
                       "--docgen-revision", api.TOOL]
            result = subprocess.run(command, cwd=archive, capture_output=True,
                                    text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("optimized Python is not supported", result.stderr)
            self.assertEqual([(archive / "docs/API.md").read_bytes(),
                              (archive / "docs/api-manifest.json").read_bytes()], targets)
            command = self.command(archive, native)
            self.assertEqual(command.returncode, 0, command.stderr)
            result = self.command(archive, native, check=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            result = subprocess.run([sys.executable, "-I", "-B",
                str(archive / "scripts/generate_api.py"), "--native-data", str(native),
                "--source-revision", api.SOURCE, "--docgen-revision", "wrong", "--check"],
                cwd=archive, capture_output=True, text=True, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unexpected/stale doc-gen4 revision", result.stderr)

    def test_source_only_archive_no_git_and_stale_outputs(self):
        with tempfile.TemporaryDirectory() as temporary:
            archive, native = self.archive(Path(temporary))
            self.assertFalse((archive / ".git").exists())
            result = self.command(archive, native)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn('"status": "matched"', result.stdout)
            (archive / "docs/api-manifest.json").write_bytes(b"{}")
            result = self.command(archive, native)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("generated file differs/stale manifest", result.stderr)
            (archive / "docs/api-manifest.json").write_bytes((ROOT / "docs/api-manifest.json").read_bytes())
            (archive / "Tests/Unexpected.lean").write_bytes(b"module\n")
            result = self.command(archive, native)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("missing/extra shipped Lean module", result.stderr)


if __name__ == "__main__":
    ARGS = PARSER.parse_args()
    unittest.main(argv=[sys.argv[0]], verbosity=2)
