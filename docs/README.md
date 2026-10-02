# Native API reference and reproducibility

The [filtered native API reference](API.md) and [machine-readable
manifest](api-manifest.json) describe an earlier 39-module source snapshot, not
the current library or its compatible-quotient modules: 24 production
leaves, one production reexport root, 13 client leaves and one client reexport
root. The 42 byte-pinned source inputs (39 Lean files and three Lean/Lake pins)
match the manifest's analyzed historical source. Its source revision/tree fields identify
the original extraction inputs, not a required checkout for using this library.
The records contain 502 production and 146 checked-use client entries; 16 of
the production entries are named instances, with 16 separate native instance
table rows. The mixed native surface includes three structures, one class,
four generated constructors, definitions/projections and theorems. Two roots
and `Tests.ProcyclicTorsionFree` have zero new named entries. The reference
preserves the native displayed headers, including independent universes, the
original source docstrings and historical source-file line anchors. Links into
the current checkout may point to shifted lines; consult the byte-pinned
historical files for source statements. Links under `Tests/` now point to
deprecated import shims; current client implementations live under
`ProfiniteGroupsTests/` with the same basenames. In 23 headers the native
pretty-printer displays Lean `⋯`; the corresponding historical source
statements preserve the original unelided source text, not unabridged
elaborated types. All 41 SQLite module-prose rows remain in the historical Lean
source, outside this filtered declaration/instance index; this is not a full
SQLite-table dump.
Exactly 132 entries
lack source docstrings and have explicitly **original catalogue explanations**
instead; these explanations are not Lean docstrings. Three generated `Fact`
names recur across seven module-local rows, counted per record rather than
deduplicated as globally exported API. Native self-links for four such rows
refer to a different module's rendered page; shipped links instead point to
the originating source file. No generated website JS, CSS, fonts,
dependency docstrings or original source assets are shipped.

This is a **filtered native declarations/instances reference**, not an
enumeration of source-private declarations or stored proof bodies. A successful
generation or adapter test is not an axiom audit, proof recheck, source-coverage
decision, rights clearance, whole-release acceptance or publication.
The [mathematical guide](Mathematics.md), especially its FreeProduct, ProP
and ProcyclicPower explanations, remains authoritative for its stated
hypotheses and limitations: maps into nonprocyclic targets are allowed where
stated, positive power-image indices **divide** the power, and no classification
of arbitrary closed subgroups is asserted.

For the current library and its pinned Mathlib revision, follow the
[quick start](../README.md#quick-start). The reproduction instructions below
apply only to the historical API-reference snapshot.

## Frozen inputs and tools

The exact SHA-256 bytes of all 39 Lean files and three Lean/Lake pins are fixed
by [`scripts/generate_api.py`](../scripts/generate_api.py) and repeated in the
[manifest](api-manifest.json). The historical extraction revision
`2417a6348d6abede2cf08f46fbb852a9f3d12d42` and tree
`0a8a4087cac28d9728c397504051cb53e4c20154` bind the native-record
source-link identity. Their presence in the manifest does not require that
Git object for source-only replays: the pinned **file bytes**, native raw records
and link identity govern the adapter. The pinned library uses Lean
`v4.34.0-rc2` and mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`.
Genuine upstream `leanprover/doc-gen4` revision
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, tree
`ebf77f3e174c145c9ca2db0df1c18a78ae87c93b`, is a separate **core-only
tool**, not a Lake dependency of this project. Do not update its pinned
manifest/toolchain while building this revision.

The historical revision supplies the **Lean source and three pins**, but its
stock adapter and manifest describe a different extraction. To check this
catalogue, stage the two adapter scripts and four documentation files from
the checkout containing this guide alongside those historical inputs. From
the root of the checkout containing this guide, make a separate worktree at
the extraction revision (fetch that revision first if it is not locally
available):

```sh
HERE=$(pwd -P)
REV=2417a6348d6abede2cf08f46fbb852a9f3d12d42
HIST=/path/to/new/historical-api-worktree
git worktree add --detach "$HIST" "$REV"
test "$(git -C "$HIST" rev-parse HEAD^{tree})" = 0a8a4087cac28d9728c397504051cb53e4c20154
cp "$HERE/scripts/generate_api.py" "$HERE/scripts/test_generate_api.py" "$HIST/scripts/"
cp "$HERE/docs/API.md" "$HERE/docs/api-manifest.json" \
  "$HERE/docs/README.md" "$HERE/docs/Mathematics.md" "$HIST/docs/"
cd "$HIST"
```

Only these six adapter/output/guide files come from the checkout containing
this guide; the 39 Lean files and `lean-toolchain`, `lakefile.toml` and
`lake-manifest.json` remain at the historical revision. Copying the current
`docs/` or `scripts/` directories wholesale would introduce extra guides
that the adapter refuses. In particular, do not copy the current library's
compatible-quotient modules or change its pins to reproduce history. An
isolated source-only copy with the same 42 pinned inputs and six staged files
also works without the historical Git object; it must have no extra Lean
modules or adapter/doc files. The staged adapter and corrected API/manifest
come from the checkout containing this guide, **not** the stock historical
checkout. Read the mathematical guide's current-only compatible-subgroup and
Sylow links in the checkout containing this guide; those linked guides do not
belong in the historical checking workspace. Verify the source/pin bytes and
the strict file inventories before building:

```sh
python3 -I -B - <<'PY'
import ast
import hashlib
import json
from pathlib import Path

manifest = json.loads(Path('docs/api-manifest.json').read_text())
adapter = {
    node.targets[0].id: ast.literal_eval(node.value)
    for node in ast.parse(Path('scripts/generate_api.py').read_text()).body
    if isinstance(node, ast.Assign) and len(node.targets) == 1
    and isinstance(node.targets[0], ast.Name)
    and node.targets[0].id in {'SOURCE', 'SOURCE_TREE', 'TOOL', 'TOOL_TREE',
                               'MODULES', 'SOURCE_INPUT_SHA256', 'NATIVE_RECORD_SHA256'}
}
assert manifest['analyzed_source_revision'] == adapter['SOURCE'] == '2417a6348d6abede2cf08f46fbb852a9f3d12d42'
assert manifest['analyzed_source_tree'] == adapter['SOURCE_TREE'] == '0a8a4087cac28d9728c397504051cb53e4c20154'
assert manifest['docgen_revision'] == adapter['TOOL'] == '97d4ecdfc8e09e7f511724c25e303d448de6a3db'
assert manifest['docgen_tree'] == adapter['TOOL_TREE'] == 'ebf77f3e174c145c9ca2db0df1c18a78ae87c93b'
assert manifest['modules'] == list(adapter['MODULES']) and len(manifest['modules']) == 39
assert manifest['inputs'] == adapter['SOURCE_INPUT_SHA256'] and len(manifest['inputs']) == 42
assert manifest['native_record_sha256'] == adapter['NATIVE_RECORD_SHA256']
assert set(manifest['normalized_record_sha256']) == set(manifest['modules'])
assert all(Path(path).is_file() and not Path(path).is_symlink()
           and hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest
           for path, digest in manifest['inputs'].items())
lean = {path.as_posix() for directory in (Path('.'), Path('ProfiniteGroups'), Path('Tests'))
        for path in directory.glob('*.lean')}
assert lean == {path for path in manifest['inputs'] if path.endswith('.lean')}
assert {path.name for path in Path('scripts').iterdir()} == {'generate_api.py', 'test_generate_api.py'}
assert {path.name for path in Path('docs').iterdir()} == {'API.md', 'api-manifest.json', 'README.md', 'Mathematics.md'}
assert manifest['api_sha256'] == 'baf24ea331bd06f2220e6bcd3762edf9c70851511e33ccf12849baf3fbc78094'
assert hashlib.sha256(Path('docs/API.md').read_bytes()).hexdigest() == manifest['api_sha256']
print('Historical source, adapter and output identities match')
PY
```

In that separate historical worktree, install its pinned Lean toolchain and
**successfully fetch its matching mathlib cache**; a failed fetch is a blocker,
never permission for an unannounced full mathlib source rebuild:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build ProfiniteGroups ProfiniteGroupsTests
```

**Optional independent native extraction (not part of the ordinary build):** clone
doc-gen4 into another separate checkout and verify its exact commit/tree. Build
`lake build doc-gen4` there with its own pinned environment; if `cc` is absent,
prepend `$(dirname "$(elan which lean)")` to `PATH`. From the separate historical
project root (not the current checkout), choose an **unused external** output
directory for a native run (never generate into the shipped repository). The
following reproduces the original native link identity using only the manifest's
historical module list:

```sh
TOOL=/path/to/separate/doc-gen4/.lake/build/bin/doc-gen4
OUT=/path/to/new/external/native-run
REV=2417a6348d6abede2cf08f46fbb852a9f3d12d42
mkdir -p "$OUT/build" "$OUT/render" "$OUT/raw" "$OUT/logs"
python3 -c 'import json; print("\n".join(json.load(open("docs/api-manifest.json"))["modules"]))' > "$OUT/modules"
while IFS= read -r module; do
  path="${module//.//}.lean"
  LEAN_NUM_THREADS=2 lake env "$TOOL" single --build "$OUT/build" "$module" \
    "$OUT/build/api.db" "https://example.invalid/commit/$REV/$path"
done < "$OUT/modules"
"$TOOL" bibPrepass --build "$OUT/render" --none
mapfile -t modules < "$OUT/modules"
"$TOOL" fromDb --build "$OUT/render" --manifest "$OUT/render/manifest.json" \
  "$OUT/build/api.db" "${modules[@]}"
for module in "${modules[@]}"; do
  cp "$OUT/render/doc-data/declaration-data-$module.bmp" "$OUT/raw/"
done
python3 -B scripts/test_generate_api.py --native-data "$OUT/raw"
python3 -B scripts/generate_api.py --native-data "$OUT/raw" \
  --source-revision "$REV" \
  --docgen-revision 97d4ecdfc8e09e7f511724c25e303d448de6a3db --check
```

For a source-only replay of the shipped output, instead supply the **original
externally retained** 39 raw native records to the staged adapter; these files
are not included in either checkout:

```sh
RAW=/path/to/original/external/raw
python3 -B scripts/test_generate_api.py --native-data "$RAW"
python3 -B scripts/generate_api.py --native-data "$RAW" \
  --source-revision "$REV" \
  --docgen-revision 97d4ecdfc8e09e7f511724c25e303d448de6a3db --check
```

Without the original external records, a replay of the shipped extraction
cannot be claimed. A fresh native run is only an independent comparison, not
a substitute for those archived records or evidence of a second historical
run. Do not fabricate missing records.

`example.invalid` is an inert native record identity, **not** a linked source
or provenance claim. Retain complete SQLite, raw records, commands, streams,
exit codes and hashes externally if doing an independent native intake;
doc-gen4's website output does not belong in this library. A fresh native
run or repeated website extraction is not a default consumer/release step.
Two historical independent runs on an earlier mathematical input produced
identical SQLite SHA-256
`5ceae54761b812e749db5b25bf8c208320cd080e673c20fb6da0d2a830c1a926`
and byte-identical contents for **all 39** historical raw records. The shipped
manifest binds a separate set of 39 raw records from one extraction of its
byte-pinned input; changed inert source-link identity changed every raw hash.
Comparison of the 35 unchanged-source modules after normalizing *only* that
link preserved every header, name, kind, source anchor, docstring and instance
row; the other four modules preserved their displayed headers, names, kinds and
instance rows, with one corrected docstring and 68 updated line anchors.
The shipped input has **one** native extraction, not a second repeatability
claim. Literal retained historical stage timestamps give sequential
native-stage wall sums of 128.577 and 126.523 seconds on those two earlier runs;
these are not performance promises. The initial cache-first
`lake --wfail build ProfiniteGroups ProfiniteGroupsTests` completed 2933 jobs,
and the separate pinned doc-gen4 build completed 194 jobs. Their respective
53.407- and 120.973-second shell timings are **author-reported**, printed to
an unretained PTY, not archived literal measurements or benchmarks. The
author also reported a 15 GiB worker cgroup `memory.max` and no OOM kills;
literal `memory.max` and `memory.events` readings were not archived. Its
historical `memory.peak` had already reached the limit during cache provisioning
and **cannot** be attributed to either build. These observations do not establish
a portable peak, minimum memory requirement or scheduler cap.
`LEAN_NUM_THREADS=2` only sets Lean's thread setting; neither `lake -Kjobs=2`,
`LAKE_JOBS` nor this variable is a verified process scheduler or total memory
cap for this pinned Lake. Keep project builds sequential and monitor actual
memory/process use. A separate earlier stored-body audit in another worker
cgroup recorded `memory.events max=705, oom=0`; successful current-source
documentation checks do not erase that pressure or turn its body findings into
native-reference evidence.

## Replay and boundaries

The adapter binds the 42 source/pin bytes, all module names/row counts,
native raw SHA-256 and normalized JSON SHA-256 for every module, the native
tool revision and tree, exact source links, file line/docstring agreement,
visible names/kinds, complete instance tables and representative implicit
binders. It rejects omissions, duplicate entries, extra native files,
active header HTML and active Markdown docstrings, altered source or tool
revision, stale outputs and Python optimization **before writing output**.
It accepts the supported native structure/class/constructor forms and the
four exact cross-module self-link collisions, without discarding them.
The [data-only corruption tests](../scripts/test_generate_api.py) are not
Lean tests; passing them cannot attest that a producer ran doc-gen4. Raw
records and full SQLite remain separate provenance for that question.

For source-only replays, retain the 42 checked source inputs, both Python scripts,
`docs/README.md`, `docs/Mathematics.md`, generated API/manifest, and the
**39 external raw records**.
The adapter does **not** need Git or the historical source commit object.
Without those external raw files, the native joins and data-only corruption
tests cannot be replayed; static reconstruction or fabricated fixtures are
not substitutes for original extraction. The native manifest is documentation
evidence, not a whole-release audit.

## Origin and boundaries

The reference and data-only tests adapt the finite-group Tate cohomology
mixed-kind catalogue via polynomial-root-stability and Anchor's
ideal-completion recipe. Formal Frontier Agents prepared the reference,
test controls and subsequent source-only refresh; Beacon coordinated the
library's readiness and API repairs. Folio contributed the mathematical
headline descriptions in the [overview](../README.md). Original project
expression and Lean source docstrings are offered under
[Apache License 2.0](../LICENSE), **Authors: Formal Frontier Agents**;
this does not invent a copyright holder. Native signatures refer to
Lean/mathlib types, but no upstream documentation, website assets or source
book files are shipped. Mathlib and doc-gen4 retain their own terms and
contributor notices. Historical origin review corrected unsupported owner
labels in Lean headers; rights, attribution and publication-history review
remain separate from adapter validation.

An optional historical `docBlameThm` run was **NONPASS** for 23 generated
equation-lemma documentation findings. These are **not** the 23 native `⋯`
headers. Owner convention disposition is recorded in the initial publication
review history; this guide does not turn that lint into a passing result or
a fresh mandatory release gate.
