# Reconstructing closed subgroups from finite quotient images

For a profinite group `G`, the library
`ProfiniteGroups.CompatibleSubgroups` uses the open normal subgroups
`U : OpenNormalSubgroup G` as the coordinates of the finite quotient system.
Its `Family G` assigns a subgroup `S U` of `G ⧸ U.toSubgroup` to every coordinate.
For `U ≤ V`, `transition G U V h` is the canonical quotient homomorphism
`G/U → G/V`, in the direction of **larger** subgroups and **smaller** quotients.
`Compatible G S` requires **equality**

```text
(S U).map (transition G U V h) = S V
```

for every such pair, not merely inclusion. In particular, this equality supplies
a lift of any prescribed member of `S V` to `S U` whenever `U ≤ V`.

`reconstruct G S` is the infimum of the quotient-preimage subgroups in `Subgroup G`;
`isClosed_reconstruct G S` establishes closedness even for an incompatible family,
and `closedReconstruction G S` is its `ClosedSubgroup G` wrapper. The theorem
`map_reconstruct G S hS U` says that **each** quotient image is exactly `S U`.
For a closed subgroup `L`, `closed_eq_iInf_images G L` recovers its underlying
subgroup from all its quotient images, `closedReconstruction_images G L` recovers
it as a closed subgroup, and `ext_images G L K h` proves uniqueness from equality
of all finite quotient images. Alternatively, `closedReconstruction_unique`
identifies any closed subgroup having the prescribed compatible images.
Closedness is essential for uniqueness: a proper dense subgroup could have the
same finite quotient images as its closure.

## Consumer example

```lean
import ProfiniteGroups.CompatibleSubgroups

open ProfiniteGrp.CompatibleSubgroups

example (G : ProfiniteGrp) (S : Family G) (hS : Compatible G S)
    (U : OpenNormalSubgroup G) :
    (closedReconstruction G S).toSubgroup.map
        (QuotientGroup.mk' U.toSubgroup) = S U :=
  map_reconstruct G S hS U

example (G : ProfiniteGrp) (L : ClosedSubgroup G) :
    closedReconstruction G
        (fun U : OpenNormalSubgroup G =>
          L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) = L :=
  closedReconstruction_images G L
```

The companion client `Tests.CompatibleSubgroups`
also tests image compatibility, the exact-image theorem for an arbitrary family,
and the bottom-family boundary case over the trivial profinite group.

See the [producer](../ProfiniteGroups/CompatibleSubgroups.lean) and
[ordinary-import client](../Tests/CompatibleSubgroups.lean) for the declarations
and examples.

## Proof ingredients and credit

The quotient system is mathlib's `ProfiniteGrp.toFiniteQuotientFunctor`,
`diagram`, and continuous `proj` in
`Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits`.
`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` refines an open
overgroup, letting `ProfiniteGrp.closedSubgroup_eq_sInf_open` separate closed
subgroups by **normal** quotient images. Algebraic saturation uses
`Subgroup.comap_map_eq` and `QuotientGroup.ker_mk'`. Exact images come from
finite common refinements and `IsCompact.inter_iInter_nonempty` on a prescribed
compact quotient fiber, including the empty finite test set; they require neither
metrizability nor countability nor a Sylow or prime assumption.

Beacon proposed the generic mathematical construction; Formal Frontier Agents
implemented it in Lean. The underlying mathlib results retain their authorship.
This quotient-image reconstruction does not assert a classification of closed
Sylow subgroups or source correspondence.
