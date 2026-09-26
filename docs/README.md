# Native API reference and reproducibility

The [filtered native API reference](API.md) and [machine-readable
manifest](api-manifest.json) describe all 39 shipped Lean modules from the
analyzed source-only predecessor `2417a6348d6abede2cf08f46fbb852a9f3d12d42`
(tree `0a8a4087cac28d9728c397504051cb53e4c20154`): 24 production leaves,
one production reexport root, 13 client leaves and one client reexport root.
The records contain 502 production and 146 checked-use client entries; 16 of
the production entries are named instances, with 16 separate native instance
table rows. The mixed native surface includes three structures, one class,
four generated constructors, definitions/projections and theorems. Two roots
and `Tests.ProcyclicTorsionFree` have zero new named entries. The reference
preserves the native displayed headers, including independent universes, the
original source docstrings and source-file line anchors. In 23 headers the
native pretty-printer displays Lean `⋯`; linked source statements preserve
the original unelided source text, not unabridged elaborated types. All 41
SQLite module-prose rows remain in the shipped Lean source, outside this
filtered declaration/instance index; this is not a full SQLite-table dump.
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
Production semantic guides in the [main README](../README.md), especially
FreeProduct, ProP and ProcyclicPower, remain authoritative for their stated
hypotheses and limitations: maps into nonprocyclic targets are allowed where
stated, positive power-image indices **divide** the power, and no classification
of arbitrary closed subgroups is asserted.

## Frozen inputs and tools

The exact SHA-256 bytes of all 39 Lean files and three Lean/Lake pins are fixed
by [`scripts/generate_api.py`](../scripts/generate_api.py) and repeated in the
[manifest](api-manifest.json). The commit and tree above label the **analyzed
source-only inputs**, directly following unaccepted `882d53f855aeeb60f02a72d5f7694438f7b3a237`;
they are not claims that the later documentation branch is that commit or that
the historical Git object exists in a source-only archive. Four Lean files
have scoped source/proof-style or docstring edits relative to that parent;
the other 35 Lean files and all three pins retain their bytes. The external
exact-head acceptance record must bind the later documentation commit and tree
separately. The pinned library uses Lean
`v4.34.0-rc2` and mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`.
Genuine upstream `leanprover/doc-gen4` revision
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, tree
`ebf77f3e174c145c9ca2db0df1c18a78ae87c93b`, is a separate **core-only
tool**, not a Lake dependency of this project. Do not update its pinned
manifest/toolchain while building this revision.

Before any library build, install the pinned Lean toolchain and **successfully
fetch the mathlib cache in this checkout**; a failed fetch is a blocker, never
permission for an unannounced full mathlib source rebuild:

```sh
elan toolchain install "$(cat lean-toolchain)"
lake exe cache get
LEAN_NUM_THREADS=2 lake --wfail build ProfiniteGroups ProfiniteGroupsTests
```

Clone doc-gen4 into a separate checkout and verify its exact commit/tree. Build
`lake build doc-gen4` there with its own pinned environment; if `cc` is absent,
prepend `$(dirname "$(elan which lean)")` to `PATH`. From the project root,
choose an **unused external** output directory for each independent native
run (never generate into the shipped repository). The following is the
replay recipe for one run, using only the manifest's shipped module list:

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

`example.invalid` is an inert native record identity, **not** a linked source
or provenance claim. Retain complete SQLite, raw records, commands, streams,
exit codes and hashes externally for independent intake; doc-gen4's website
output does not belong in this library. Re-run with a second fresh directory
and compare all raw records and SQLite, not merely receipt digests. The two
earlier independent runs on the **previous** accepted mathematical input
`3b6c142d7e127b057f5cd54902d24f10fd3fe5cf` produced identical SQLite SHA-256
`5ceae54761b812e749db5b25bf8c208320cd080e673c20fb6da0d2a830c1a926`
and byte-identical contents for **all 39** historical raw records. The current
manifest instead binds **39 newly generated** source-only predecessor records;
their inert source-link identity changes every raw record hash. Comparing the
35 unchanged-source modules with the historical records after normalizing
*only* that link preserves every header, name, kind, source anchor, docstring
and instance row. The four edited modules also preserve all displayed headers,
names, kinds and instance rows, with one corrected source docstring and 68
updated line anchors. This is one current-source native run, **not** a second
repeatability claim. Literal retained historical stage timestamps give sequential
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

For source-only replays, retain the 42 checked source inputs, adapter,
`docs/README.md`, generated API/manifest, and the 39 external raw records.
The adapter does **not** need Git or the historical source commit object.
The original isolated parentless same-tree replay and no-Git archive test
applied to the historical documentation candidate; the current-source
adapter controls and native joins require their own exact-candidate evidence. The
current development-branch status in this guide is dated **2026-09-26**;
later release status belongs in an external exact-commit lifecycle record.

## Origin, credit and rights

This wording and lifecycle correction was prepared by worker-b Hive Task
`hive-request-1706c2a7c232d243b2552dc0fc1e1b44eac183cd`, UID
`20fbc411-a19e-45aa-bf2d-326a3d1ea887`, Hive launch request
`4a7f373610195a111038d48b7afeed25`; it does not claim authorship of
the underlying catalogue or acceptance of the candidate. The source-only
successor and its native-reference refresh were prepared by worker-b Hive Task
`hive-request-305d448654f8080cbf83a1723f1406bfbef7f38a`, UID
`e0c21780-f6f5-475d-987f-c7594b1e807e`; this also is not acceptance.
The original
catalogue and adapter were prepared by worker-b Hive Task
`hive-request-49578d0143b3fe26e93ee6e54fa1752f1d60bc26`, UID
`e4f64178-9024-4fe9-8eba-f63c724e7497`, from accepted finite-group Tate
cohomology revision `61577f7cf2e02715f621a724aa692921ab6bbad9`.
That donor's mixed-kind generator/tests were authored by worker-b Task
`hive-request-381dc6f93292eb39ea2d5b25f09baacdc8b20d9e`, UID
`cd8c84f8-2dbf-4399-9c70-1de364ffa99f`, adapting the accepted
polynomial-root-stability expression `95ac896f81a3190b2634a4246a3e924d2a267a61`
and Anchor's ideal-completion recipe `f0c8c34386109116e4912fb425a8ad15d9dc42a4`.
These project expressions and original Lean source docstrings are credited
under [Apache License 2.0](../LICENSE), **Authors: Formal Frontier Agents**;
this is not an assertion of an invented copyright holder. The native
signatures refer to Lean/mathlib types but copy no upstream documentation or
website assets. The mathlib and doc-gen4 dependency tools retain their own
terms and contributor notices in their separate checkouts; the cited NSW
book supplies mathematical motivation only, and its private source files are
not bundled. Existing project-origin investigation identified 15 historical
unsupported owner labels already corrected in the current Lean headers;
that correction does **not** by itself clear rights in the complete candidate
or future public squash history. At the September 26 documentation-author
checkpoint, whole-artifact expression/antecedent, third-party
notices/redistribution and proposed publication-history review had not been
established; later decisions need external exact-commit records. The
separately recorded optional `docBlameThm` check was **NONPASS** for 23
generated equation-lemma documentation findings, distinct from the 23 native
`⋯` headers above; owner/fresh-review convention disposition was outstanding
at that checkpoint. Earlier ordinary mathematics reviews and this Task's
authorship are not whole-release acceptance.
