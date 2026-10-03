# Compatible Sylow families of profinite finite quotients

`ProfiniteGroups.CompatibleSylow` constructs, for any profinite group
`G : ProfiniteGrp` and prime natural number `p`, a compatible choice of Sylow
`p`-subgroups of **all** quotients by open normal subgroups. Its strongest
existence result, `G.exists_compatibleSylowFamily_with p hp U P`, takes an
arbitrary open normal `U` and an arbitrarily prescribed
`P : Sylow p (G ⧸ (U : Subgroup G))`, and produces a family whose coordinate
at `U` is exactly `P`. No countability, metrizability, finite-generation or
continuity hypothesis beyond the profinite group is imposed.

The [producer](../ProfiniteGroups/CompatibleSylow.lean) and
[ordinary-import client](../ProfiniteGroupsTests/CompatibleSylow.lean)
give the exact declarations and examples.

## Public API

- `G.compatibleSylow p hp` is the functor assigning the finite set of Sylow
  subgroups to every open-normal quotient.
- `G.CompatibleSylowFamily p hp` is its type of compatible sections;
  `s.at U` evaluates a section, `CompatibleSylowFamily.ext` determines families
  from their values at every quotient, `s.map_at f` expresses functorial
  compatibility, and `s.map_at_subgroup h` states the corresponding
  subgroup-image equality.
- `G.exists_compatibleSylowFamily_with p hp U P` extends any prescribed
  coordinate. `G.exists_compatibleSylowFamily p hp` gives an unprescribed family.
- `CompatibleSylow.system` and `CompatibleSylow.exists_system_with` also work
  for any cofiltered diagram of finite groups whose arrows are surjective.

For example, with a public import of `ProfiniteGroups.CompatibleSylow`:

```lean
example (G : ProfiniteGrp) (p : ℕ) (hp : p.Prime)
    (U : OpenNormalSubgroup G) (P : Sylow p (G ⧸ (U : Subgroup G))) :
    ∃ s : G.CompatibleSylowFamily p hp, s.at U = P := by
  exact G.exists_compatibleSylowFamily_with p hp U P
```

The index category orders open normal subgroups by inclusion. For `U ≤ V`,
`G/U → G/V` is a surjective arrow **from the finer quotient to the coarser
quotient**. Hence the associated Sylow functor is covariant on this cofiltered
index, and the section condition is that the image of `s.at U` is `s.at V`.
In particular, nothing requires an inverse image of a Sylow subgroup to itself
be Sylow: the lifting of Sylow choices uses finite Sylow theory instead.
The client also prescribes a Sylow subgroup in each quotient of the trivial
profinite group and verifies independently that its image is the whole quotient.

## Construction and credit

The canonical diagram is mathlib's `ProfiniteGrp.toFiniteQuotientFunctor`.
Surjectivity of its transition maps follows by lifting a representative from
`G` through `QuotientGroup.mk_surjective`. For each finite quotient, mathlib's
`Sylow.mapSurjective` produces its Sylow transition and
`Sylow.mapSurjective_surjective` lifts a prescribed coordinate. The existence
of compatible choices and surjectivity of evaluation reuse respectively
`nonempty_sections_of_finite_cofiltered_system` and
`CategoryTheory.Functor.eval_section_surjective_of_surjective`, with no new
finite Sylow or compactness argument. The native profinite diagram is due to
Nailin Guan, Youle Fang, Jujian Zhang and Yuyang Zhao; the finite-cofiltered
system results credit Kyle Miller, Adam Topaz, Rémi Bottinelli and Junyan Xu;
mathlib's Sylow library credits Chris Hughes and Thomas Browning. This
development builds on their work.

Formal Frontier Agents developed the Lean construction and examples, with
mathematical and documentation contributions from Beacon.

The [closed Sylow image construction](closed-sylow.md) reconstructs a closed
subgroup of `G` from this quotient-level family and proves maximality among
containing subgroups whose actual finite quotient images are `p`-groups. It
does not assert that the reconstructed subgroup is an abstract `p`-group or
establish a pro-`p` equivalence. Sylow conjugacy and cohomological applications
are separate questions.
