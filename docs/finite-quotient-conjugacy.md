<!--
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-->

# Detecting conjugacy of closed subgroups by finite quotients

Import [`ProfiniteGroups.FiniteQuotientConjugacy`](../ProfiniteGroups/FiniteQuotientConjugacy.lean) for the namespace
`ProfiniteGrp.FiniteQuotientConjugacy`. For a profinite group `G` and arbitrary
**closed** subgroups `H K : ClosedSubgroup G`, the main theorem
`exists_conjugator_iff_forall_quotients G H K` identifies an ambient conjugator
`g : G` with *existence* of a conjugator in each finite open-normal quotient.
The forward implication sends `g` to its image in each quotient. The converse
does not assume that the quotient conjugators form a compatible family.

```lean
import ProfiniteGroups.FiniteQuotientConjugacy

open ProfiniteGrp.FiniteQuotientConjugacy

example (G : ProfiniteGrp) (H K : ClosedSubgroup G)
    (h : ∀ U : OpenNormalSubgroup G, ∃ a : G ⧸ U.toSubgroup,
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).map
          (MulAut.conj a).toMonoidHom =
        K.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) :
    ∃ g : G, H.toSubgroup.map (MulAut.conj g).toMonoidHom = K.toSubgroup :=
  (exists_conjugator_iff_forall_quotients G H K).mpr h
```

`exists_conjugator_of_forall_quotients G H K h` is the standalone converse.
Here `MulAut.conj g` conjugates by `g` (sending `x` to `g * x * g⁻¹`), and
`QuotientGroup.mk' U.toSubgroup : G →* G ⧸ U.toSubgroup` maps to a finite,
discrete quotient. The order `U ≤ V` induces `G/U → G/V`: conjugation and
subgroup images commute with this transition in the **small-to-large normal
subgroup** direction. The equality of quotient subgroup images is exact, not an
inclusion. Neither `H` nor `K` must be open, normal, or of finite index.

For each `U`, the conjugators in `G` whose image in `G/U` takes the image of
`H` onto the image of `K` form a closed subset of compact `G`, since it is the
preimage of a subset of a discrete quotient. To satisfy any *nonempty* finite
set `F` of constraints, use the finite infimum of the members of `F` as a
common open-normal refinement `W`. Lift a quotient conjugator at `W` to `G`;
transition naturality satisfies every coordinate in `F`. For *empty* `F`, the
identity in `G` is already a witness; the proof handles it separately.
Compactness produces one global `g`. Its conjugate of `H` is closed because
conjugation is a homeomorphism, and
`ProfiniteGrp.CompatibleSubgroups.ext_images` identifies the two closed
subgroups from their identical quotient images. No inverse-limit choice,
countable basis, or compatible conjugator family enters the argument.

The [ordinary-import companion](../ProfiniteGroupsTests/FiniteQuotientConjugacy.lean)
`ProfiniteGroupsTests.FiniteQuotientConjugacy` exercises both
directions: the forward direction uses an ambient identity conjugator, while
the converse constructs identity conjugators independently in every quotient
for equal closed subgroups and invokes the standalone theorem to recover an
ambient conjugator. It also shows that all closed subgroups of
`ProfiniteGrp.of PUnit` are equal. This last example does **not** stand in for
the empty `Finset` step of the generic proof.

The closed-subgroup separation API is provided by
[`ProfiniteGroups.CompatibleSubgroups`](compatible-subgroups.md).
Mathlib provides open-normal subgroup infima, quotient maps and surjectivity,
`MulAut.conj`, `Subgroup.map` and compactness.

Formal Frontier Agents formalized this criterion with AI assistance. The
closed-subgroup reconstruction theorem `CompatibleSubgroups.ext_images` and
the Mathlib APIs above were prior dependencies, not results of this formalization.
