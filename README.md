# Profinite groups

Reusable Lean theory for profinite groups and finite-space diagrams:
categorical and finite-quotient maps,
closed coset spaces and normal quotients, closed-subgroup reconstruction,
compatible Sylow families and closed subgroups
with Sylow finite images, finite-quotient conjugacy, continuous sections,
free products, primewise p-adic models, procyclic
classification, and power images. The [mathematical guide](docs/Mathematics.md)
explains the constructions and limitations; the [historical native API](docs/API.md)
documents an earlier snapshot, with a [reproduction guide](docs/README.md).
The library builds on mathlib's profinite categories, completions, p-adic
integers and general algebra/topology, and on Group Theory's open-quotient
theorem.

## Headline results

Explore [finite diagrams](#finite-diagrams-and-inverse-limit-characterizations),
[maps and constructions](#maps-closed-subgroups-and-universal-constructions),
[product models and classification](#primewise-models-product-ideals-and-procyclic-classification),
and [homomorphisms, powers and coefficients](#homomorphisms-powers-and-coefficients).

### Finite diagrams and inverse-limit characterizations

- **Skeletal finite quotients and equivalence.** Every profinite space in the
  same universe is the limit of its included skeletal finite-quotient diagram.
  The associated dual ind-object realizes to that space, giving an equivalence
  between dual ind-objects of finite sets and profinite spaces whose forward
  functor is the [profinite realization](ProfiniteGroups/IndDualRealization.lean).
  The generic inverse's chosen object is compared with the skeletal presentation
  by an isomorphism. Empty spaces and
  finite stages are allowed; no arbitrary diagram projection is assumed
  surjective. See [`IndDualEquivalence`](ProfiniteGroups/IndDualEquivalence.lean)
  and its [clients](ProfiniteGroupsTests/IndDualEquivalence.lean).

- **Finite-stage inverse-limit characterizations.** A Hausdorff space is an
  inverse limit of finite discrete spaces over a small, nonempty cofiltered
  category if and only if it is compact with a clopen basis, equivalently
  compact and totally disconnected. A topological group is an inverse limit
  of finite groups over such a category if and only if it is compact and
  totally disconnected (`FiniteGroupPresentation.nonempty_iff`). For a Hausdorff
  topological group, this is also equivalent to compactness with an
  identity-neighborhood basis of open normal subgroups. The presentations use the
  actual inverse-limit topology and include empty spaces and trivial groups;
  arbitrary finite-stage projections need not be surjective. See
  [`FiniteDiscreteCharacterization`](ProfiniteGroups/FiniteDiscreteCharacterization.lean)
  and [`FiniteGroupCharacterization`](ProfiniteGroups/FiniteGroupCharacterization.lean).

### Maps, closed subgroups and universal constructions

- **Finite maps and morphisms.** In profinite groups, categorical monomorphisms
  are injective and epimorphisms are surjective. For groups in the *same
  universe*, continuous Hom is the limit over finite target quotients of the
  colimits over finite source quotients. Separately, injective and surjective
  maps of profinite **spaces** have finite-map limit presentations, not a
  finite-presentation theorem for groups. See [`EpiMono`](ProfiniteGroups/EpiMono.lean),
  [`FiniteQuotientHom`](ProfiniteGroups/FiniteQuotientHom.lean),
  [`FinitePresentation`](ProfiniteGroups/FinitePresentation.lean).

- **Closed-subgroup conjugacy.** Two closed subgroups of a profinite group
  are conjugate precisely when their images are conjugate in every finite
  open-normal quotient. The quotient conjugators need not form a compatible
  family; no countability or openness assumption is used. See
  [`FiniteQuotientConjugacy`](ProfiniteGroups/FiniteQuotientConjugacy.lean)
  and its [guide](docs/finite-quotient-conjugacy.md).

- **Continuous sections.** For closed `K ≤ H` in a profinite group, the
  projection `G/K → G/H` has a continuous right inverse; a supporting result
  supplies sections of surjective local homeomorphisms over compact Hausdorff
  totally disconnected spaces. For any closed `H`, a chosen bundled continuous
  map `G/H → G` selects a representative of each coset. The choice is neither
  asserted to be homomorphic nor normalized at the identity; normality is not
  needed. See [`ContinuousSection`](ProfiniteGroups/ContinuousSection.lean) and
  [`ContinuousCosetRepresentative`](ProfiniteGroups/ContinuousCosetRepresentative.lean).

### Primewise models, product ideals and procyclic classification

- **Procyclic classification and realization.** Given proofs of procyclicity,
  groups in independent universes are continuously equivalent exactly when
  their generator-independent primewise exponents agree. Every exponent
  family is realized by residue factors `ZMod (p^n)` and p-adic factors: zero
  exponent is trivial, infinity retains the full p-adic factor. With a
  supplied generator, torsion-freeness means all exponents are zero or
  infinity. For a torsion-free procyclic profinite group, its all-primes
  quotient model, and hence the group itself, is continuously equivalent to
  the product of p-adic integer factors over the infinite-exponent primes,
  with zero-exponent coordinates omitted. The support can be empty or infinite
  and is generator-independent; the group equivalence uses a chosen
  topological generator. The invariant is noncomputable and *not* assigned to
  arbitrary nonprocyclic groups; generator independence equates kernel ideals
  and exponents, not the associated maps. See
  [`ProcyclicInvariant`](ProfiniteGroups/ProcyclicInvariant.lean),
  [`ProcyclicRealization`](ProfiniteGroups/ProcyclicRealization.lean),
  [`ProcyclicTorsionFree`](ProfiniteGroups/ProcyclicTorsionFree.lean) and
  [`ProcyclicTorsionFreeProduct`](ProfiniteGroups/ProcyclicTorsionFreeProduct.lean).

### Homomorphisms, powers and coefficients

- **Power images and open subgroups.** For a procyclic group, positive `n`th
  powers form an open subgroup with cyclic finite quotient and index
  *dividing* `n`, not necessarily equal to `n`. Every open subgroup equals
  the power image at its actual index. The zero-power image is trivial and
  need not be open; no arbitrary-procyclic closed-subgroup classification is
  asserted. See [`ProcyclicPower`](ProfiniteGroups/ProcyclicPower.lean).

- **Closed subgroups of procyclic groups.** Every closed subgroup of an
  arbitrary procyclic profinite group is procyclic in its inherited group and
  topology, without an openness or finite-index assumption. It has a generator
  inside the subgroup whose integral powers are dense there. The result also
  accepts an ordinary subgroup with a closedness proof. It does not classify
  arbitrary closed subgroups by exponents. See
  [`ProcyclicClosedSubgroup`](ProfiniteGroups/ProcyclicClosedSubgroup.lean).

[All results and their hypotheses](docs/Results.md) ·
[Mathematical details, hypotheses and API limitations](docs/Mathematics.md).

## Quick start

Add the library to your `lakefile.toml`:

```toml
[[require]]
name = "profinite-groups"
git = "https://github.com/FormalFrontier/profinite-groups.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves it when you add or update
the dependency; `lake-manifest.json` keeps that commit until another update.
For a reproducible fixed version, replace `main` with the full commit of a
published release. Other Formal Frontier libraries and the incubator use the
GitHub URL and full published release commit, not a moving ref or PR head.
Use the release's Lean toolchain and a common Mathlib revision across dependencies:
Lake resolves only one version of each package in a build.

Install [elan](https://github.com/leanprover/elan) and Git. For this checkout,
[`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml) and
[`lake-manifest.json`](lake-manifest.json) record the Lean version and resolved
Mathlib and Group Theory dependencies. From the project root:

```sh
lake exe cache get
lake --wfail build ProfiniteGroups ProfiniteGroupsTests
```

Do not build from mathlib source if the matching cache fetch fails.
`ProfiniteGroupsTests` includes every regression and public client under
`ProfiniteGroupsTests.*`. The former `Tests.*` client import paths remain as
deprecated public-import shims. In a workspace that also requires a package
whose library owns the entire `Tests` prefix, Lake may resolve those old imports
to that package instead; use `ProfiniteGroupsTests.*` or the aggregation root
in composed projects. Use `import ProfiniteGroups` for every production leaf or
import an individual module. `ProfiniteGroups.ContinuousSection` publicly
re-exports `GroupTheory.Topology.OpenQuotient`: the canonical
`Topology.IsOpenQuotientMap.totallyDisconnectedSpace` is available from either
import without changing existing `ProfiniteGroups.ContinuousSection` clients.
For example, save the following as `Client.lean` and run
`lake env lean -DwarningAsError=true Client.lean` after the build:

```lean
import ProfiniteGroups

open CategoryTheory ProfiniteGrp
universe u

example (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (n : ℕ) (hn : 0 < n) :
    (powerImage G hG n : Subgroup G).index ∣ n :=
  powerImage_index_dvd G hG n hn

example {G H : ProfiniteGrp.{u}} (f : G ⟶ H) :
    Mono f ↔ Function.Injective f :=
  ProfiniteGrp.mono_iff_injective f
```

The first result needs a procyclicity proof and a *positive* power; the
second is categorical and same-universe. The checked-in clients contain
additional examples. For targeted checks, including optional `-T0`, see the
[client-checking instructions](docs/Mathematics.md#checking-a-client); for build
resource caveats, see the [reproduction guide](docs/README.md#build-resources).

For finite-diagram and dual-ind-object API applications, see the
[usage guide](docs/Usage.md).

## Module map

[`ProfiniteGroups.lean`](ProfiniteGroups.lean) publicly imports every production
leaf below; no `Tests` module is part of the production root.

| Mathematics | Importable modules |
| --- | --- |
| Finite-stage inverse-limit characterizations | [`FiniteDiscreteCharacterization`](ProfiniteGroups/FiniteDiscreteCharacterization.lean), [`FiniteGroupCharacterization`](ProfiniteGroups/FiniteGroupCharacterization.lean) |
| Finite-space limit stages and map comparisons | [`FiniteStageImages`](ProfiniteGroups/FiniteStageImages.lean), [`FiniteTargetHomColimit`](ProfiniteGroups/FiniteTargetHomColimit.lean), [`FiniteDiagramHomLimit`](ProfiniteGroups/FiniteDiagramHomLimit.lean), [`FiniteDiagramIndDual`](ProfiniteGroups/FiniteDiagramIndDual.lean), [`IndDualRealization`](ProfiniteGroups/IndDualRealization.lean), [`IndDualEquivalence`](ProfiniteGroups/IndDualEquivalence.lean) |
| Category and finite maps | [`EpiMono`](ProfiniteGroups/EpiMono.lean), [`FiniteQuotientHom`](ProfiniteGroups/FiniteQuotientHom.lean), [`FinitePresentation`](ProfiniteGroups/FinitePresentation.lean), [`ContinuousSection`](ProfiniteGroups/ContinuousSection.lean), [`ContinuousCosetRepresentative`](ProfiniteGroups/ContinuousCosetRepresentative.lean), [`ClosedQuotient`](ProfiniteGroups/ClosedQuotient.lean) |
| Finite-quotient subgroups and Sylow images | [`CompatibleSubgroups`](ProfiniteGroups/CompatibleSubgroups.lean), [`CompatibleSylow`](ProfiniteGroups/CompatibleSylow.lean), [`ClosedSylow`](ProfiniteGroups/ClosedSylow.lean), [`FiniteQuotientConjugacy`](ProfiniteGroups/FiniteQuotientConjugacy.lean) |
| Universal profinite groups | [`FreeProduct`](ProfiniteGroups/FreeProduct.lean), [`ProP`](ProfiniteGroups/ProP.lean) |
| Cyclic completion and product | [`Procyclic`](ProfiniteGroups/Procyclic.lean), [`PrimewisePadic`](ProfiniteGroups/PrimewisePadic.lean), [`PrimewisePadicKernel`](ProfiniteGroups/PrimewisePadicKernel.lean), [`IntegerPadicResidueLimit`](ProfiniteGroups/IntegerPadicResidueLimit.lean) |
| Product ideals and factor models | [`ClosedIdealPi`](ProfiniteGroups/ClosedIdealPi.lean), [`PrimewisePadicIdeals`](ProfiniteGroups/PrimewisePadicIdeals.lean), [`PiIdealQuotient`](ProfiniteGroups/PiIdealQuotient.lean), [`PrimewisePadicQuotients`](ProfiniteGroups/PrimewisePadicQuotients.lean), [`PrimewisePadicSubgroups`](ProfiniteGroups/PrimewisePadicSubgroups.lean) |
| Universe and generator transport | [`ProcyclicBaseMap`](ProfiniteGroups/ProcyclicBaseMap.lean), [`PrimewisePadicIdealTransport`](ProfiniteGroups/PrimewisePadicIdealTransport.lean), [`PrimewisePadicKernelTransport`](ProfiniteGroups/PrimewisePadicKernelTransport.lean), [`ProcyclicGeneratorIndependence`](ProfiniteGroups/ProcyclicGeneratorIndependence.lean) |
| Quotients and classification | [`ProcyclicQuotient`](ProfiniteGroups/ProcyclicQuotient.lean), [`ProcyclicInvariant`](ProfiniteGroups/ProcyclicInvariant.lean), [`ProcyclicRealization`](ProfiniteGroups/ProcyclicRealization.lean), [`ProcyclicTorsionFree`](ProfiniteGroups/ProcyclicTorsionFree.lean), [`ProcyclicTorsionFreeProduct`](ProfiniteGroups/ProcyclicTorsionFreeProduct.lean), [`ProcyclicSupportProduct`](ProfiniteGroups/ProcyclicSupportProduct.lean) |
| Maps, power images and closed subgroups | [`ProcyclicHom`](ProfiniteGroups/ProcyclicHom.lean), [`ProcyclicPower`](ProfiniteGroups/ProcyclicPower.lean), [`ProcyclicPowerIndex`](ProfiniteGroups/ProcyclicPowerIndex.lean), [`ProcyclicPowerTransition`](ProfiniteGroups/ProcyclicPowerTransition.lean), [`ProcyclicPowerIndices`](ProfiniteGroups/ProcyclicPowerIndices.lean), [`ProcyclicPowerLimit`](ProfiniteGroups/ProcyclicPowerLimit.lean), [`ProcyclicResidueLimit`](ProfiniteGroups/ProcyclicResidueLimit.lean), [`ProcyclicClosedSubgroup`](ProfiniteGroups/ProcyclicClosedSubgroup.lean) |
| Additive coefficients at prime-supported indices | [`PrimeSupportedCoefficients`](ProfiniteGroups/PrimeSupportedCoefficients.lean) |

## References

- J. Neukirch, A. Schmidt and K. Wingberg, [*Cohomology of Number Fields*,
  corrected second edition, electronic v2.3 (May 2020)](https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/),
  Ch. I §1 (Lemma (1.1.1), Proposition (1.1.3), Exercises 1 and 3–5), §6
  (finite-quotient pro-`p` and Sylow constructions), and §7 before (1.7.7)
  (procyclic groups, completed integers, p-adic products and supported powers).
- [Mathlib](https://github.com/leanprover-community/mathlib4/tree/83abb3e776bdefcbc447a1e44d0debe4010039e5),
  pinned revision `83abb3e776bdefcbc447a1e44d0debe4010039e5`:
  `Profinite.AsLimit`, `Profinite.Extend`, `ProfiniteGrp.Limits`,
  `ProfiniteGrp.Completion`, Indization/presentation, `CoprodI`, `Sylow`,
  p-adic integers, ideal quotients and categorical/topological APIs.
- [Group Theory](https://github.com/FormalFrontier/group-theory/tree/77c1f2663514f8d43db606d3eb3409533a6e29a5),
  pinned revision `77c1f2663514f8d43db606d3eb3409533a6e29a5`:
  `GroupTheory.Topology.OpenQuotient` houses the generic open-quotient theorem
  first formalized here and used for profinite coset spaces.

## Scope and credit

This source-independent library has separate production and test roots. The
closed-coset construction does not make a nonnormal quotient a group, and the
normal-quotient universal property assumes that the subgroup lies in the
homomorphism's kernel; the dual-Ind/profinite equivalence concerns spaces,
not profinite group objects or an arbitrary pro-category.
Mathematical correspondence and coverage of particular sources are recorded outside this library.
The cited characterizations and exercises in Neukirch–Schmidt–Wingberg supply
mathematical origins for the corresponding results; other constructions use its
finite-system, Sylow and procyclic discussions as motivation rather than asserting
every local refinement is a printed theorem. In particular, Sylow finite images
are not identified here with the book's index-defined `p`-Sylow subgroups.
The book is not shipped source material and these citations make no coverage claim.

Original Lean mathematics and client tests were developed by Formal Frontier
Agents, including Beacon's initial implementation, later mathematical and test
contributors, and Beacon's library assembly and targeted API repairs.
The library follows Mathlib's finite quotients, Ind presentations, profinite
completion, finite Sylow groups and p-adic/ideal APIs as detailed in the module
references, as well as using the cited mathematical sources.
The reference adapter and catalogue were adapted through the finite-group
Tate cohomology, polynomial-root-stability and Anchor ideal-completion work;
Folio supplied the scoped headline documentation. AI agents contributed code,
proofs, documentation, checks and independent reviews. Original project
expression is offered under [Apache-2.0](LICENSE), **Authors: Formal Frontier
Agents**. Mathlib and doc-gen4 retain their own license and attribution.
No copyright holder is inferred from this collective credit.
