# Profinite groups

Reusable Lean theory for profinite groups: categorical and finite-quotient maps,
closed coset spaces and normal quotients, closed-subgroup reconstruction,
compatible Sylow families and closed subgroups
with Sylow finite images, finite-quotient conjugacy, continuous sections,
free products, primewise p-adic models, procyclic
classification, and power images. The [mathematical guide](docs/Mathematics.md)
explains the constructions and limitations; the [historical native API](docs/API.md)
documents an earlier snapshot, with a [reproduction guide](docs/README.md).
The library builds on mathlib's profinite categories, completions, p-adic
integers and general algebra/topology.

## Headline results

- **Finite maps and morphisms.** In profinite groups, categorical monomorphisms
  are injective and epimorphisms are surjective. For groups in the *same
  universe*, continuous Hom is the limit over finite target quotients of the
  colimits over finite source quotients. Separately, injective and surjective
  maps of profinite **spaces** have finite-map limit presentations, not a
  finite-presentation theorem for groups. See [`EpiMono`](ProfiniteGroups/EpiMono.lean),
  [`FiniteQuotientHom`](ProfiniteGroups/FiniteQuotientHom.lean),
  [`FinitePresentation`](ProfiniteGroups/FinitePresentation.lean).
- **Finite-quotient subgroups and Sylow families.** Compatible subgroup images
  in every open-normal quotient reconstruct a unique closed subgroup, with
  **equality** at each coordinate. For every prime `p`, a compatible Sylow
  family exists on all such quotients even with an arbitrarily prescribed
  Sylow subgroup at any one quotient. Each such family reconstructs a closed
  subgroup with **exactly** those Sylow images. A subgroup containing this
  reconstruction equals it if all its actual finite quotient images are
  `p`-groups, even if that subgroup is not closed. This is not an assertion
  that its underlying abstract subgroup is an algebraic `p`-group. See
  [`CompatibleSubgroups`](ProfiniteGroups/CompatibleSubgroups.lean) and its
  [guide](docs/compatible-subgroups.md), and
  [`CompatibleSylow`](ProfiniteGroups/CompatibleSylow.lean) and its
  [guide](docs/compatible-sylow.md), and
  [`ClosedSylow`](ProfiniteGroups/ClosedSylow.lean) and its
  [guide](docs/closed-sylow.md).
- **Closed-subgroup conjugacy.** Two closed subgroups of a profinite group
  are conjugate precisely when their images are conjugate in every finite
  open-normal quotient. The quotient conjugators need not form a compatible
  family; no countability or openness assumption is used. See
  [`FiniteQuotientConjugacy`](ProfiniteGroups/FiniteQuotientConjugacy.lean)
  and its [guide](docs/finite-quotient-conjugacy.md).
- **Continuous sections.** For closed `K ≤ H` in a profinite group, the
  projection `G/K → G/H` has a continuous right inverse; a supporting result
  supplies sections of surjective local homeomorphisms over compact Hausdorff
  totally disconnected spaces. These maps are not asserted to be homomorphic
  splittings, and normality is not needed. See
  [`ContinuousSection`](ProfiniteGroups/ContinuousSection.lean).
- **Closed cosets and group quotients.** A closed subgroup has a profinite
  coset space with the quotient topology, without a normality assumption.
  A closed normal subgroup also has a profinite group quotient, with a
  surjective continuous projection whose kernel is the subgroup. Forgetting
  the group structure recovers the coset space and its projection. Every
  continuous homomorphism to a profinite group in the same universe that kills
  the normal subgroup factors uniquely through the group quotient. Neither
  construction assumes openness or finite index. See
  [`ClosedQuotient`](ProfiniteGroups/ClosedQuotient.lean).
- **Free profinite and pro-`p` constructions.** Arbitrary families admit a free
  profinite product with injective factor maps and a continuous universal
  mapping property. For prime `p`, the maximal pro-`p` quotient and free
  pro-`p` products have the stated universal properties; factors of the latter
  may be arbitrary profinite groups, but factor *injectivity* requires every
  factor to be pro-`p`. Targets use the specified `max u v` universe, with no
  finite-family restriction. See [`FreeProduct`](ProfiniteGroups/FreeProduct.lean)
  and [`ProP`](ProfiniteGroups/ProP.lean).
- **Primewise completed integers.** The profinite completion of the infinite
  cyclic group is continuously equivalent to the multiplicatively written
  product of additive `p`-adic integers, whose integral diagonal is dense.
  Closed subgroups of **this particular product** are classified by primewise
  `ℕ∞` exponents in *reversed* order: zero gives the full coordinate and
  infinity the zero subgroup. See [`PrimewisePadic`](ProfiniteGroups/PrimewisePadic.lean)
  and [`PrimewisePadicSubgroups`](ProfiniteGroups/PrimewisePadicSubgroups.lean).
- **Closed product ideals and quotients.** A closed ideal of a product of
  semirings with topologies is the product of its coordinate images, without
  extra separation or topology/operation compatibility; closedness is
  essential. Separately, product-ideal quotients of commutative rings are
  products of coordinate quotients, with a continuous additive equivalence
  for topological rings. This quotient construction requires neither
  closedness nor a nonempty/finite index type. See
  [`ClosedIdealPi`](ProfiniteGroups/ClosedIdealPi.lean) and
  [`PiIdealQuotient`](ProfiniteGroups/PiIdealQuotient.lean).
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
- **Maps with prescribed generator image.** Given a procyclic source and a
  supplied topological generator `g`, a specified `h` in *any profinite target*
  extends uniquely to a continuous homomorphism sending `g` to `h` exactly
  when the kernel exponents of the common-source map for `h` lie below the
  source exponents. Surjectivity requires `h` to generate the target. The
  inequality does not characterize the mere existence of an unspecified
  homomorphism. See [`ProcyclicHom`](ProfiniteGroups/ProcyclicHom.lean).
- **Power images and open subgroups.** For a procyclic group, positive `n`th
  powers form an open subgroup with cyclic finite quotient and index
  *dividing* `n`, not necessarily equal to `n`. Every open subgroup equals
  the power image at its actual index. The zero-power image is trivial and
  need not be open; no arbitrary-procyclic closed-subgroup classification is
  asserted. See [`ProcyclicPower`](ProfiniteGroups/ProcyclicPower.lean).
- **Exact positive-power indices.** For procyclic `G` and positive `n`, the
  index of the `n`th-power subgroup equals `n` exactly when each prime
  multiplicity in `n` is bounded by the corresponding primewise exponent of
  `G`. Given a topological generator and this exact-index condition, its class
  in the quotient determines a continuous multiplicative equivalence from
  `Multiplicative (ZMod n)`; the forward and inverse generator equations are
  available. For torsion-free procyclic `G`, the positive exact-index criterion
  is membership in the submonoid generated by its infinite-exponent primes;
  every open-subgroup index belongs to this submonoid. These exponents are
  generator-independent. See
  [`ProcyclicPowerIndex`](ProfiniteGroups/ProcyclicPowerIndex.lean) and
  [`ProcyclicPowerIndices`](ProfiniteGroups/ProcyclicPowerIndices.lean).
- **Power-quotient transitions.** For a procyclic profinite group `G`, if
  `d ∣ n`, inclusion of power images gives a surjective continuous
  homomorphism from the `n`th-power quotient to the
  `d`th-power quotient, preserving classes and satisfying identity and
  composition laws without an index assumption. If the source has exact index
  `n > 0`, the target has exact index `d`; equivalences normalized by the same
  topological generator identify this map with reduction `ZMod n → ZMod d`.
  See [`ProcyclicPowerTransition`](ProfiniteGroups/ProcyclicPowerTransition.lean).
- **Closed subgroups of procyclic groups.** Every closed subgroup of an
  arbitrary procyclic profinite group is procyclic in its inherited group and
  topology, without an openness or finite-index assumption. It has a generator
  inside the subgroup whose integral powers are dense there. The result also
  accepts an ordinary subgroup with a closedness proof. It does not classify
  arbitrary closed subgroups by exponents. See
  [`ProcyclicClosedSubgroup`](ProfiniteGroups/ProcyclicClosedSubgroup.lean).

[Mathematical details, hypotheses and API limitations](docs/Mathematics.md).

## Quick start

Install [elan](https://github.com/leanprover/elan) and Git. The pinned
[`lean-toolchain`](lean-toolchain) selects Lean `v4.34.0-rc2`;
[`lake-manifest.json`](lake-manifest.json) pins mathlib at
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. From the project root:

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
import an individual module. For example, save the following as `Client.lean` and run
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
additional examples. For optional targeted `-T0` and historical resource
observations, see the [reproduction guide](docs/README.md).

## Module map

[`ProfiniteGroups.lean`](ProfiniteGroups.lean) publicly imports every production
leaf below; no `Tests` module is part of the production root.

| Mathematics | Importable modules |
| --- | --- |
| Category and finite maps | [`EpiMono`](ProfiniteGroups/EpiMono.lean), [`FiniteQuotientHom`](ProfiniteGroups/FiniteQuotientHom.lean), [`FinitePresentation`](ProfiniteGroups/FinitePresentation.lean), [`ContinuousSection`](ProfiniteGroups/ContinuousSection.lean), [`ClosedQuotient`](ProfiniteGroups/ClosedQuotient.lean) |
| Finite-quotient subgroups and Sylow images | [`CompatibleSubgroups`](ProfiniteGroups/CompatibleSubgroups.lean), [`CompatibleSylow`](ProfiniteGroups/CompatibleSylow.lean), [`ClosedSylow`](ProfiniteGroups/ClosedSylow.lean), [`FiniteQuotientConjugacy`](ProfiniteGroups/FiniteQuotientConjugacy.lean) |
| Universal profinite groups | [`FreeProduct`](ProfiniteGroups/FreeProduct.lean), [`ProP`](ProfiniteGroups/ProP.lean) |
| Cyclic completion and product | [`Procyclic`](ProfiniteGroups/Procyclic.lean), [`PrimewisePadic`](ProfiniteGroups/PrimewisePadic.lean), [`PrimewisePadicKernel`](ProfiniteGroups/PrimewisePadicKernel.lean) |
| Product ideals and factor models | [`ClosedIdealPi`](ProfiniteGroups/ClosedIdealPi.lean), [`PrimewisePadicIdeals`](ProfiniteGroups/PrimewisePadicIdeals.lean), [`PiIdealQuotient`](ProfiniteGroups/PiIdealQuotient.lean), [`PrimewisePadicQuotients`](ProfiniteGroups/PrimewisePadicQuotients.lean), [`PrimewisePadicSubgroups`](ProfiniteGroups/PrimewisePadicSubgroups.lean) |
| Universe and generator transport | [`ProcyclicBaseMap`](ProfiniteGroups/ProcyclicBaseMap.lean), [`PrimewisePadicIdealTransport`](ProfiniteGroups/PrimewisePadicIdealTransport.lean), [`PrimewisePadicKernelTransport`](ProfiniteGroups/PrimewisePadicKernelTransport.lean), [`ProcyclicGeneratorIndependence`](ProfiniteGroups/ProcyclicGeneratorIndependence.lean) |
| Quotients and classification | [`ProcyclicQuotient`](ProfiniteGroups/ProcyclicQuotient.lean), [`ProcyclicInvariant`](ProfiniteGroups/ProcyclicInvariant.lean), [`ProcyclicRealization`](ProfiniteGroups/ProcyclicRealization.lean), [`ProcyclicTorsionFree`](ProfiniteGroups/ProcyclicTorsionFree.lean), [`ProcyclicTorsionFreeProduct`](ProfiniteGroups/ProcyclicTorsionFreeProduct.lean) |
| Maps, power images and closed subgroups | [`ProcyclicHom`](ProfiniteGroups/ProcyclicHom.lean), [`ProcyclicPower`](ProfiniteGroups/ProcyclicPower.lean), [`ProcyclicPowerIndex`](ProfiniteGroups/ProcyclicPowerIndex.lean), [`ProcyclicPowerTransition`](ProfiniteGroups/ProcyclicPowerTransition.lean), [`ProcyclicPowerIndices`](ProfiniteGroups/ProcyclicPowerIndices.lean), [`ProcyclicClosedSubgroup`](ProfiniteGroups/ProcyclicClosedSubgroup.lean) |

## Scope and credit

This source-independent library has separate production and test roots. The
closed-coset construction does not make a nonnormal quotient a group, and the
normal-quotient universal property assumes that the subgroup lies in the
homomorphism's kernel; no equivalence with a pro-category is asserted.
Mathematical correspondence and coverage of particular sources are recorded outside this library.
[Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
edition, electronic version 2.3 (May 2020)](https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/)
is mathematical background, not shipped source material or a coverage claim.

Original Lean mathematics and client tests were developed by Formal Frontier
Agents, including Beacon's initial implementation, later mathematical and test
contributors, and Beacon's readiness integration and targeted API repairs.
The reference adapter and catalogue were adapted through the finite-group
Tate cohomology, polynomial-root-stability and Anchor ideal-completion work;
Folio supplied the scoped headline documentation. AI agents contributed code,
proofs, documentation, checks and independent reviews. Original project
expression is offered under [Apache-2.0](LICENSE), **Authors: Formal Frontier
Agents**. Mathlib and doc-gen4 retain their own license and attribution.
No copyright holder is inferred from this collective credit.
