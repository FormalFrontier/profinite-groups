# Using finite diagrams and dual ind-objects

[Back to the overview and build instructions](../README.md#quick-start).

Import `ProfiniteGroups` to use the following interfaces.

For a cofiltered finite diagram `F`, a limiting cone `c` with proof `hc`,
and a finite target `S`, use `Profinite.stageHomEquiv c hc S` to convert
stage-map classes to continuous maps. Its `stageHomEquiv_apply_class` lemma
computes a representative by composing its stage map with the projection;
`stageHomNatIso c hc` packages postcomposition in the finite target.
For a finite-space target diagram `G` with limiting cone `d` and proof `hd`,
`Profinite.stageHomLimitEquiv F c hc G d hd` converts a continuous map between
the cone points into compatible stage-map classes. Its inverse projection is
computed by `stageHomLimitEquiv_symm_apply_projection` and, on a representative,
by `stageHomLimitEquiv_symm_apply_class`.

For an object `Q : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ`, use
`Profinite.indDualRealization.obj Q` for its profinite realization and
`Profinite.indDualRealizationHomEquiv Q R` to convert its morphisms to
continuous maps. `Profinite.indDualRealizationComparison X c hc` compares a
diagram-induced object with a specified limiting cone, while
`Profinite.indDualRealizationComparisonOfIso X e c hc` accepts an arbitrary
supplied presentation isomorphism; `Profinite.indDualRealizationPresentationIso`
composes such comparisons between supplied presentations.
Use `Profinite.indDualEquivalence` for the fixed-universe equivalence and
`Profinite.skeletalQuotientIndDual T` for a specified inverse model of a
profinite space `T`. The isomorphism `Profinite.skeletalQuotientRealizationIso T`
realizes this model as `T`; `Profinite.indDualEquivalenceInverseIso T` compares
it with the equivalence's generic inverse.
