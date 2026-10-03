# Closed Sylow images in profinite finite quotients

For `G : ProfiniteGrp` and a prime natural number `p` (`hp : p.Prime`),
`ProfiniteGroups.ClosedSylow` turns a compatible family of Sylow
`p`-subgroups of **every** quotient by an open normal subgroup into a closed
subgroup of `G`. The image in `G ⧸ U.toSubgroup` is *equal* to that family's
chosen Sylow subgroup at `U`, not merely contained in it. All quotient maps
are `QuotientGroup.mk' U.toSubgroup`; arrows from `U ≤ V` run from the
finer `G/U` to the coarser `G/V`. No sequence, countability or metrizability
assumption enters the construction.

The [producer](../ProfiniteGroups/ClosedSylow.lean) and
[client examples](../ProfiniteGroupsTests/ClosedSylow.lean)
give the statements and public-use examples. With `s : G.CompatibleSylowFamily p hp`,
`s.closedSubgroup` reconstructs the subgroup; `s.map_closedSubgroup U` proves
the exact image and `s.isPGroup_image U` its finite-image `IsPGroup p` property.
`G.exists_closedSylow p hp` gives a closed subgroup with Sylow images at every
coordinate. `G.exists_closedSylow_with p hp U Q` additionally realizes **any**
prescribed `Q : Sylow p (G ⧸ U.toSubgroup)` as its image at `U`.

`ProfiniteGrp.eq_closedSylow_of_le_of_isPGroup_images P hP H hPH hH`
asserts bounded maximality: if `P` is closed and has Sylow images at every
open-normal quotient (`hP`), `P.toSubgroup ≤ H` (`hPH`), and **each actual image**
`H.map (QuotientGroup.mk' U.toSubgroup)` is `IsPGroup p` (`hH`), then
`H = P.toSubgroup`. It does not require `H` to be closed. At each quotient,
Mathlib's `Sylow.is_maximal'` forces equality of the images by `Subgroup.map_mono`;
`CompatibleSubgroups.closed_eq_iInf_images` then recovers the
inclusion `H ≤ P.toSubgroup`. In particular, a compatible-family reconstruction
is maximal under those exact hypotheses. The existence constructions require
`hp : p.Prime`; the conditional maximality theorem itself needs no separate
prime argument once its Sylow-image witnesses are supplied.

The [client examples](../ProfiniteGroupsTests/ClosedSylow.lean) apply bounded
maximality to a subgroup containing a compatible-family reconstruction. They
also construct a quotient Sylow independently for `PUnit`, realize that
prescribed image using `exists_closedSylow_with`, and identify the resulting
subgroup with `⊤`. The `IsPGroup p` assertions concern ambient **finite
quotient images**. Neither the abstract subgroup `P.toSubgroup` nor its
subtype is asserted to be an algebraic `p`-group, and no general pro-`p`
criterion for its intrinsic finite quotients is formalized here.
No converse maximality theorem, containment of arbitrary pro-`p` subgroups,
conjugacy, index result or cohomology application follows from this API.

## Construction and credit

The construction composes the compatible sections from
[`ProfiniteGroups.CompatibleSylow`](compatible-sylow.md) with the exact-image
reconstruction from
[`ProfiniteGroups.CompatibleSubgroups`](compatible-subgroups.md). It reuses these
dependencies and Mathlib's finite Sylow maximality and subgroup-map results.
This implementation and guide are authored by Formal Frontier Agents (AI agents).
