# Profinite groups

Reusable Lean theory for profinite groups, from categorical morphisms and
finite quotients through primewise p-adic models and procyclic power images.
The [native API reference](docs/API.md) indexes every shipped Lean module;
its [reproduction guide](docs/README.md) describes exact pinned inputs,
limits, verified native-stage timings and author-reported build costs.

## Quick start

Install [elan](https://github.com/leanprover/elan), Git and Lake (supplied by
the Lean toolchain), then clone this repository. The exact inputs are
[`lean-toolchain`](lean-toolchain) (Lean `v4.34.0-rc2`) and
[`lake-manifest.json`](lake-manifest.json) (mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103`). From the root:

```sh
lake exe cache get
lake build ProfiniteGroups ProfiniteGroupsTests
```

**Stop if the matching mathlib cache fetch fails**; do not silently compile
mathlib from source. The named `ProfiniteGroupsTests` target (added with the
default-target/test-module readiness changes) checks all existing tests and
root-only and direct-leaf public clients. Import `ProfiniteGroups` for the
full API, or import an individual leaf to minimize dependencies. Here is a
client file, e.g. `Client.lean`, checked with
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

The first result needs a supplied `IsProcyclic` proof and a **positive** power;
the index *divides* `n` and need not equal it. The second is an equivalence
for categorical monomorphisms of profinite groups in the same universe.

In a September 26, 2026 local check of this representative client, ordinary
`lake env lean -DwarningAsError=true` took 2.862 seconds and the `-T0` variant
took 2.861 seconds; both exited successfully with no output. Sampling their
descendant process trees every 100 ms found maximum observed RSS of 845864
and 845728 KiB, respectively. These are single local measurements, not
continuous peaks or portable memory minima: imports were already compiled and
the matching mathlib cache had been fetched. The separate cgroup readings
include other processes and cached files, and neither the measurements nor a
Lake job setting establishes a scheduler or memory cap. See the separately
retained native and stored-body resource evidence in the reproduction guide;
these client observations do not erase its reported pressure.

## Module map

[`ProfiniteGroups.lean`](ProfiniteGroups.lean) publicly imports every production
leaf below; no `Tests` module is part of the production root.

| Mathematics | Importable modules |
| --- | --- |
| Category and finite maps | [`EpiMono`](ProfiniteGroups/EpiMono.lean), [`FiniteQuotientHom`](ProfiniteGroups/FiniteQuotientHom.lean), [`FinitePresentation`](ProfiniteGroups/FinitePresentation.lean), [`ContinuousSection`](ProfiniteGroups/ContinuousSection.lean) |
| Universal profinite groups | [`FreeProduct`](ProfiniteGroups/FreeProduct.lean), [`ProP`](ProfiniteGroups/ProP.lean) |
| Cyclic completion and product | [`Procyclic`](ProfiniteGroups/Procyclic.lean), [`PrimewisePadic`](ProfiniteGroups/PrimewisePadic.lean), [`PrimewisePadicKernel`](ProfiniteGroups/PrimewisePadicKernel.lean) |
| Product ideals and factor models | [`ClosedIdealPi`](ProfiniteGroups/ClosedIdealPi.lean), [`PrimewisePadicIdeals`](ProfiniteGroups/PrimewisePadicIdeals.lean), [`PiIdealQuotient`](ProfiniteGroups/PiIdealQuotient.lean), [`PrimewisePadicQuotients`](ProfiniteGroups/PrimewisePadicQuotients.lean), [`PrimewisePadicSubgroups`](ProfiniteGroups/PrimewisePadicSubgroups.lean) |
| Universe and generator transport | [`ProcyclicBaseMap`](ProfiniteGroups/ProcyclicBaseMap.lean), [`PrimewisePadicIdealTransport`](ProfiniteGroups/PrimewisePadicIdealTransport.lean), [`PrimewisePadicKernelTransport`](ProfiniteGroups/PrimewisePadicKernelTransport.lean), [`ProcyclicGeneratorIndependence`](ProfiniteGroups/ProcyclicGeneratorIndependence.lean) |
| Quotients and classification | [`ProcyclicQuotient`](ProfiniteGroups/ProcyclicQuotient.lean), [`ProcyclicInvariant`](ProfiniteGroups/ProcyclicInvariant.lean), [`ProcyclicRealization`](ProfiniteGroups/ProcyclicRealization.lean), [`ProcyclicTorsionFree`](ProfiniteGroups/ProcyclicTorsionFree.lean) |
| Maps and open power images | [`ProcyclicHom`](ProfiniteGroups/ProcyclicHom.lean), [`ProcyclicPower`](ProfiniteGroups/ProcyclicPower.lean) |

## Mathematical scope

The repository is organized around reusable mathematics rather than any one
source. Source-specific interpretation, provenance, and coverage remain in the
corresponding source-metadata repositories.

The category API characterizes monomorphisms of profinite groups, and of
profinite additive groups, by injectivity of their underlying functions. It
also characterizes epimorphisms of profinite groups by surjectivity, using
finite quotients for the nontrivial direction.

The same-universe finite-quotient homomorphism API gives an explicit equivalence
`Hom(G, H) ≃ lim_V colim_U Hom(G/U, H/V)`: the inner filtered colimit is
represented by agreement after common refinement, and the outer limit by
compatible families over the finite quotients of `H`.
Finite-stage interpretation and its injection into continuous homomorphisms
work for any group equipped with a topology: continuity comes from the discrete
finite **source** quotient. The inverse construction through an open kernel,
and hence the two-sided equivalence for a general target type, still require
the target to be discrete.

The continuous-section API shows that a surjective local homeomorphism over a
profinite space has a section. In particular, `G/T → G/S` has a continuous
section when `S` is closed and `T` is open in `S`, and the projection
`G/K → G/H` has a continuous section for arbitrary closed subgroups `K ≤ H`.
The API also packages the strict refinement step used in the maximal-section
argument for closed coset spaces.

The finite-presentation API represents every injective or surjective map of
profinite spaces as the map of limits of a cofiltered system of respectively
injective or surjective maps between finite discrete spaces.

The procyclic API defines topological generators by dense integral powers (or
integral multiples), constructs the canonical map from the profinite completion
of the infinite cyclic group, identifies its range with the closure of those
powers, and characterizes generators by surjectivity and epimorphy. It also
provides transport under continuous homomorphisms and equivalences, quotient
closure, trivial-group cases, and standard finite cyclic examples in both
multiplicative and additive form. Mathlib's pinned profinite-completion API does
not currently expose the additive universal `lift` and `lift_eta`, so the
additive-native completion-map counterpart is intentionally deferred rather
than reconstructed from finite quotients here.

The primewise p-adic API constructs the universe-polymorphic product of the
additive groups of the p-adic integers, written multiplicatively.  The integral
diagonal is dense by the Chinese remainder theorem, so the element with every
coordinate equal to `1` topologically generates the product.  Consequently the
canonical map from the profinite completion of the integers onto this product is
an equivalence of topological groups.  Injectivity is proved by factoring every
finite quotient coordinate through a residue ring and applying prime-power
Chinese remainder decomposition.

The primewise p-adic kernel API also exposes the underlying product ring and
its dense integer casts.  A generic bridge turns any closed additive subgroup
of a topological ring with dense integer casts into a left ideal.  Applied to
the closed kernel of an arbitrary continuous multiplicative homomorphism out of
the primewise p-adic group, this gives a closed kernel ideal without requiring
surjectivity or any classification of closed ideals of an infinite product.

The primewise common-source API changes the universe of the product by a
coordinate-preserving continuous group equivalence. Every element of a
profinite group determines a continuous map from the universe-zero product,
surjective for topological generators and natural under arbitrary continuous
homomorphisms. This does not identify generator-dependent kernel exponents
across universes; that compatibility requires separate ideal transport.

The closed-product-ideal API gives the complementary generic classification:
every closed ideal in an arbitrary product of topological semirings is the
product of its coordinate images.  No compatibility between topology and ring
operations or separation assumption is needed.  Closedness is essential:
for an infinite product, the ideal of finitely supported elements is generally
not a product of coordinate ideals.

Combining this product theorem with the discrete-valuation-ring ideal
classification gives an `ℕ∞` exponent for every ideal in an uplifted p-adic
factor and a primewise exponent family for every closed ideal in the primewise
p-adic ring.  The factor order is explicitly reversed: exponent zero is the
top ideal and exponent `⊤` is the zero ideal.  The API reconstructs every
closed product ideal, proves uniqueness of its exponents, and keeps the
construction universe-polymorphic.

Changing the `ULift` universe of each p-adic factor gives a coordinate-preserving
ring equivalence of the primewise product. It preserves coordinate-ideal
exponents under image and preimage for every ideal, not only closed ideals,
and commutes with the product ideals made from prescribed exponents. Only
closed product ideals are determined by their exponents; this algebraic
transport makes no assertion about kernel maps or group classification.

The continuous primewise group universe change and algebraic ring universe
change agree under the multiplicative identifications. Precomposing any
continuous homomorphism into a T1 group pulls its kernel ideal back along the
ring equivalence and preserves its primewise exponents, without requiring
surjectivity. In particular, the fixed-source map of *every* element, whether
or not it is a generator, has the same exponent family as its original map.
This comparison does not define a generator-free invariant or classify targets.

Closed additive subgroups of the primewise p-adic ring are therefore likewise
classified by primewise `ℕ∞` exponents.  The classification is an order
isomorphism to the dual pointwise order: larger exponents mean smaller
subgroups.  The continuous multiplicative equivalence transports this API to
closed subgroups of the primewise p-adic profinite group, with explicit
coordinate membership and uniqueness theorems.  For every continuous
multiplicative homomorphism into an arbitrary T1 group, its kernel ideal is
reconstructed from the resulting exponents; all exponents are infinite exactly
for an injective map, and all are zero exactly for the trivial map.

The product-ideal quotient API identifies, for an arbitrary dependent family
of commutative topological rings and an arbitrary (possibly empty) index type,
the quotient by a product ideal with the product of the coordinate quotients.
It provides coherent ring and continuous additive equivalences without
closedness, separation, compactness, or finiteness assumptions. Its p-adic
specialization identifies finite exponent factors with `ZMod (p^n)` (including
`n = 0`), infinite exponent factors with the uplifted p-adic integers, and
arbitrary mixed primewise quotients with a universe-polymorphic product of
these profinite factor models.

A supplied topological generator of a profinite group also determines a
surjective homomorphism from the primewise p-adic product. The continuous
first-isomorphism bridge identifies the multiplicatively written quotient by
its kernel ideal with the group itself; the kernel's exponent family then
identifies the group with the product of finite-residue and p-adic factors.
[ProcyclicQuotient](ProfiniteGroups/ProcyclicQuotient.lean) gives explicit
integral-diagonal, quotient-representative, and coordinate formulas. Its
exponent family is computed using the supplied generator. The
[generator-independence theorem](ProfiniteGroups/ProcyclicGeneratorIndependence.lean)
shows that any two topological generators give equal kernel ideals and exponent
families, although their associated maps need not be equal.

[ProcyclicInvariant](ProfiniteGroups/ProcyclicInvariant.lean) packages the
generator-independent exponent family as `IsProcyclic.exponents` from a
*supplied proof* of procyclicity; selecting its internal generator is
noncomputable. `IsProcyclic.exponents_eq_of_generator` identifies this family
with the existing exponents for every genuine topological generator, and
`IsProcyclic.continuousMulEquivModel` identifies the group with the fixed
universe-zero product quotient specified by its exponents. For two groups
already known to be procyclic, in arbitrary and independent universes,
`isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq` characterizes the
existence of a topological multiplicative equivalence by equality of these
families. No invariant is assigned to nonprocyclic groups.

[ProcyclicRealization](ProfiniteGroups/ProcyclicRealization.lean) realizes every
`e : Nat.Primes → ℕ∞` in any universe using the existing product model:
`primewisePadicProcyclicModel e` is its multiplicative presentation, and
`primewisePadicRealizationMap e` is a continuous surjection from the primewise
p-adic group with actual kernel `primewisePadicIdealOfExponents e`. The map
has quotient-representative and diagonal coordinate formulas (finite exponents
reduce modulo `p ^ k`; infinite exponents retain p-adic casts). Its image
`primewisePadicRealizationGenerator e` of the additive-one diagonal generates
the model; additive zero maps to the multiplicative identity. For *every*
procyclicity proof `h`, `primewisePadicProcyclicModel_exponents e h` proves
`h.exponents = e`. `exists_procyclic_of_exponents` packages arbitrary-universe
existence, and `primewisePadicProcyclicModel_nonempty_equiv_iff` classifies
these models in independent universes by equality of their profiles. The
finite/top mixed-coordinate lemmas use heterogeneous equality when their
  coordinate types depend on an exponent equality. No nonprocyclic invariant
  or supernatural-number packaging is asserted.

The [continuous procyclic homomorphism API](ProfiniteGroups/ProcyclicHom.lean)
uses a **supplied** topological generator `g : G` and procyclicity proof `hG`.
For **any** profinite target `H`, even a nonprocyclic one, and any `h : H`,
`existsUnique_continuousHom_apply_generator_iff hG g hg h` identifies existence
and uniqueness of a continuous `f : G →ₜ* H` with `f g = h` with the condition
`∀ p, primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator H h) p ≤
hG.exponents p`. Only the *source* has a generator-independent invariant: the
target exponents belong to the common-source map attached to `h`.
`factorOfGenerator` constructs this map; `factorOfGenerator_comp_baseMap` proves
its commuting square, and `continuousHom_ext_of_generator` proves uniqueness.
The factor is surjective exactly if `h` generates `H`, via
`factorOfGenerator_surjective_iff`. For two already-procyclic groups in
independent universes, `exists_surjective_continuousHom_iff_exponents_le`
characterizes continuous quotients by pointwise exponent inequality. The
identity, identity-image and composition laws are `factorOfGenerator_self`,
`factorOfGenerator_one`, and `factorOfGenerator_comp`. For example the trivial
image is always admissible but its map need not be onto; **mere existence of
some homomorphism** is never characterized by the inequality. The tracked
proof-use tests also construct an admissible identity image in the nonprocyclic
finite Klein group and a nonsurjective C4 endomorphism mapping a generator to
  its square.

The [procyclic power API](ProfiniteGroups/ProcyclicPower.lean) takes an arbitrary
`G : ProfiniteGrp.{u}` with a *supplied* `hG : IsProcyclic G`. The actual
continuous endomorphism `powerHom G hG n` sends `x` to `x ^ n`;
`powerImage G hG n : ClosedSubgroup G` is its compact, closed range, with
membership `∃ y, y ^ n = x`. For every supplied topological generator `g`,
`powerImage_eq_topologicalClosure_zpowers` identifies its subgroup with the
topological closure of `Subgroup.zpowers (g ^ n)`. The continuous surjection
`powerHomToImage` supplies the actual generator and procyclicity of the range,
viewed through `ofClosedSubgroup` as a profinite group. Both the map and range
are definitionally independent of the proof chosen for `hG`. The zero-th image is
`⊥` and the first image is `⊤`; no openness is asserted for the zero-th image.

For `0 < n`, `powerImage_index_dvd` proves the image has finite index **dividing**
`n`, and `powerImage_isOpen` / `powerOpenSubgroup` give an open-subgroup interface.
The quotient is finite cyclic, with the class of `g` generating it
(`powerImage_quotient_zpowers_eq_top`). Every `H : OpenSubgroup G` satisfies
`openSubgroup_eq_powerImage G hG H`, namely `H.toSubgroup = powerImage G hG
H.toSubgroup.index`; `subgroup_eq_powerImage_of_isOpen` accepts an ordinary
`Subgroup` plus an openness proof. Open subgroups of equal index are equal.
The index is **not** necessarily `n`: fourth powers in `C₂` have index `2`,
squares in `C₃` are surjective (index `1`), and squares in `C₄` have index
`2`. Neither closed-subgroup classification nor numerical allowed-index or
primewise exponent formulas are included; additive users can use the existing
`Additive`/`Multiplicative` bridges.

The primewise quotient factors and their product are additively torsion-free
exactly when every exponent is zero or infinite: zero gives a trivial residue
factor, while a positive finite exponent contributes nonzero torsion. This
criterion transfers to arbitrary surjective continuous images of the primewise
p-adic group and to profinite groups with a supplied topological generator,
using the exponent family computed from that supplied generator.

More precisely, the pinned mathlib revision accepts
`ProfiniteAddGrp.ProfiniteCompletion.completion (AddGrpCat.of ℤ)` and
`ProfiniteAddGrp.ProfiniteCompletion.denseRange`, but the following direct
probe fails with `Unknown constant` for both names:

```lean
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
#check ProfiniteAddGrp.ProfiniteCompletion.lift
#check ProfiniteAddGrp.ProfiniteCompletion.lift_eta
```

Here `ℤ` is the additive infinite cyclic group. `Additive ℤ` would instead
derive addition from integer multiplication and is not an additive group.

## Development and status

After fetching the matching cache, use `lake build ProfiniteGroups
ProfiniteGroupsTests` for the named targets (both are configured as defaults
in the assembled readiness change). Existing regression clients, including
[`Tests/ProcyclicPower.lean`](Tests/ProcyclicPower.lean), additionally support
`lake env lean -DwarningAsError=true Tests/ProcyclicPower.lean` and the
`-T0` variant. Development contributors should keep Lean and mathlib pinned,
preserve the import/public visibility contract, add direct public-client tests
for changed APIs, and submit changes for fresh independent review.

The readiness update removes unused discreteness assumptions from the forward
finite-quotient maps (including the intermediate target of `HomColimit.postcomp`)
and the unused `IsTopologicalRing` assumption from equality-of-ideals transport.
Existing inferred applications and defining values are preserved; code supplying
all typeclass arguments positionally with `@` must account for the removed binders.
The named integer and zero/one-power laws remain available. Their redundant simp
attributes are removed; power-coordinate automation uses the normalized
`procyclicContinuousMulEquivModel_zsmul_apply` law, with the original zpow law
retained by name. Root-import tests check plain-simp computations and defining
values without adding the removed assumptions back.

Original Formal Frontier contributions are offered under
[Apache License 2.0](LICENSE); [`formalization.yaml`](formalization.yaml) records
repository metadata. **Authors: Formal Frontier Agents.** Original project
expression includes earlier work by Beacon and later worker-a/worker-b
executions. Mathematical constructions use mathlib at the pinned revision;
its upstream license and attribution remain applicable. AI agents assisted
with proofs, code, documentation, verification and review; prior mathematical
PR reviews are not whole-artifact release approval. Other provenance and
third-party obligations require their own review. At the **2026-09-26
documentation-author snapshot**, a complete 39-module filtered native
reference and its reproducibility manifest had been prepared, but that
candidate had not received independent exact-head acceptance. At that
checkpoint the first internal release had not been accepted: complete rights
and whole-artifact review, full raw/private/stored-body proof and axiom
certification, separate proof rechecking, and owner acceptance were not
established. Historical ordinary-main approvals are dated evidence for their
exact earlier commits, not a live release registry. Later independent review,
owner acceptance and publication are external exact-commit decisions, not
inferred from this historical snapshot. No generated website is promised here.

The library stands on its own; detailed source-passage correspondence and
source formalization status belong to the source's records, not this library.
