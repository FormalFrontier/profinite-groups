# Native API reference (historical snapshot)

This catalogue describes 39 Lean modules from an earlier, byte-pinned
library snapshot, not this checkout or its compatible-quotient modules.
The historical graph used Lean `v4.34.0-rc2`, mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` and independent doc-gen4 `97d4ecdfc8e09e7f511724c25e303d448de6a3db`;
the current library pins mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`.
All entries, counts and line anchors below refer to the historical source.
Links into this checkout may have shifted; consult the byte-pinned historical
source when interpreting an anchor. Links under `Tests/` now point to deprecated
import shims; current client implementations live under `ProfiniteGroupsTests/`.
This is a filtered native reference: 502 production and 146 checked-use
client entries, including structures, a class, constructors, projections,
instances, definitions and theorems. Full native displayed signatures
retain implicit parameters, typeclasses and independent universes.
The source anchors identify historical Lean files. Entries without
source docstrings receive clearly marked original catalogue explanations.
The two reexport roots and one test leaf have zero new named entries.
In 23 headers the native pretty-printer displays Lean `⋯`; the corresponding
historical source statements preserve original unelided source text, not
unabridged elaborated types. The 41 SQLite module-prose rows remain
in historical Lean source, outside this filtered declaration/instance
index; this is not a full SQLite-table dump.
This is not a census of private declarations or proof fields and does
not certify axioms, proofs, source coverage, rights or release acceptance.
[Reproduction and limitations](README.md).

## Production API

### ProfiniteGroups

0 native named entries; 0 native instance-table rows.

No new named declarations in this module.

### ProfiniteGroups.ClosedIdealPi

1 native named entries; 0 native instance-table rows.

#### Ideal.eq_pi_map_evalRingHom_of_isClosed

Kind: `theorem`.

```lean
theorem Ideal.eq_pi_map_evalRingHom_of_isClosed {ι : Type u} {R : ι → Type v} [(i : ι) → Semiring (R i)] [(i : ι) → TopologicalSpace (R i)] (I : Ideal ((i : ι) → R i)) (hI : IsClosed ↑I) : I = pi fun (i : ι) => map (Pi.evalRingHom R i) I
```

**Native source docstring:** A closed ideal in a product of topological semirings is the product of its
coordinate images.

No compatibility between the topology and the semiring operations, and no
separation, compactness, or nonemptiness assumption, is needed.

[Source](../ProfiniteGroups/ClosedIdealPi.lean#L27) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.ContinuousSection

10 native named entries; 1 native instance-table rows.

#### Topology.IsOpenQuotientMap.totallyDisconnectedSpace

Kind: `theorem`.

```lean
theorem Topology.IsOpenQuotientMap.totallyDisconnectedSpace {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [T2Space Y] {f : X → Y} (hf : IsOpenQuotientMap f) : TotallyDisconnectedSpace Y
```

**Native source docstring:** An open Hausdorff quotient of a compact Hausdorff totally disconnected
space is totally disconnected.

[Source](../ProfiniteGroups/ContinuousSection.lean#L43) (native source start line; generated entries may point to their parent).

#### QuotientGroup.instTotallyDisconnectedSpace

Kind: `instance`.

```lean
instance QuotientGroup.instTotallyDisconnectedSpace {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {S : Subgroup G} [IsClosed ↑S] : TotallyDisconnectedSpace (G ⧸ S)
```

**Native source docstring:** The coset space of a profinite group by a closed subgroup is totally
disconnected.

[Source](../ProfiniteGroups/ContinuousSection.lean#L64) (native source start line; generated entries may point to their parent).

#### IsLocalHomeomorph.exists_continuous_section_of_surjective

Kind: `theorem`.

```lean
theorem IsLocalHomeomorph.exists_continuous_section_of_surjective {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B] {p : E → B} (hp : IsLocalHomeomorph p) (hsurj : Function.Surjective p) : ∃ (s : B → E), Continuous s ∧ Function.RightInverse s p
```

**Native source docstring:** A surjective local homeomorphism over a profinite space has a continuous
section.

[Source](../ProfiniteGroups/ContinuousSection.lean#L75) (native source start line; generated entries may point to their parent).

#### Subgroup.quotientMapOfLE_isLocallyInjective_of_isOpen

Kind: `theorem`.

```lean
theorem Subgroup.quotientMapOfLE_isLocallyInjective_of_isOpen {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {T S : Subgroup G} (hTS : T ≤ S) (hT : IsOpen ↑(T.subgroupOf S)) : IsLocallyInjective (quotientMapOfLE hTS)
```

**Native source docstring:** If `T` is open in `S`, the projection `G ⧸ T → G ⧸ S` is locally
injective.

[Source](../ProfiniteGroups/ContinuousSection.lean#L123) (native source start line; generated entries may point to their parent).

#### Subgroup.quotientMapOfLE_isLocalHomeomorph_of_isOpen

Kind: `theorem`.

```lean
theorem Subgroup.quotientMapOfLE_isLocalHomeomorph_of_isOpen {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {T S : Subgroup G} (hTS : T ≤ S) (hT : IsOpen ↑(T.subgroupOf S)) : IsLocalHomeomorph (quotientMapOfLE hTS)
```

**Native source docstring:** If `T` is open in `S`, the projection `G ⧸ T → G ⧸ S` is a local
homeomorphism.

[Source](../ProfiniteGroups/ContinuousSection.lean#L159) (native source start line; generated entries may point to their parent).

#### Subgroup.quotientMapOfLE_exists_continuous_section_of_isOpen

Kind: `theorem`.

```lean
theorem Subgroup.quotientMapOfLE_exists_continuous_section_of_isOpen {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {T S : Subgroup G} [CompactSpace (G ⧸ S)] [T2Space (G ⧸ S)] [TotallyDisconnectedSpace (G ⧸ S)] (hTS : T ≤ S) (hT : IsOpen ↑(T.subgroupOf S)) : ∃ (s : G ⧸ S → G ⧸ T), Continuous s ∧ Function.RightInverse s (quotientMapOfLE hTS)
```

**Native source docstring:** If `T` is open in `S` and `G ⧸ S` is profinite, the projection
`G ⧸ T → G ⧸ S` has a continuous section.

[Source](../ProfiniteGroups/ContinuousSection.lean#L181) (native source start line; generated entries may point to their parent).

#### Subgroup.quotientMapOfLE_exists_continuous_section

Kind: `theorem`.

```lean
theorem Subgroup.quotientMapOfLE_exists_continuous_section {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {T S : Subgroup G} [IsClosed ↑S] (hTS : T ≤ S) (hT : IsOpen ↑(T.subgroupOf S)) : ∃ (s : G ⧸ S → G ⧸ T), Continuous s ∧ Function.RightInverse s (quotientMapOfLE hTS)
```

**Native source docstring:** If `S` is closed and `T` is open in `S`, the profinite coset projection
`G ⧸ T → G ⧸ S` has a continuous section.

[Source](../ProfiniteGroups/ContinuousSection.lean#L194) (native source start line; generated entries may point to their parent).

#### Subgroup.exists_intermediate_open_subgroupOf_of_lt

Kind: `theorem`.

```lean
theorem Subgroup.exists_intermediate_open_subgroupOf_of_lt {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {K S : Subgroup G} [IsClosed ↑K] [IsClosed ↑S] (hKS : K < S) : ∃ (T : Subgroup G), K ≤ T ∧ T < S ∧ IsClosed ↑T ∧ IsOpen ↑(T.subgroupOf S)
```

**Native source docstring:** Between a closed subgroup `K` and a strictly larger closed subgroup `S`
of a profinite group, there is a closed intermediate subgroup that is open
and proper in `S`.

[Source](../ProfiniteGroups/ContinuousSection.lean#L204) (native source start line; generated entries may point to their parent).

#### Subgroup.exists_strict_continuous_section_refinement

Kind: `theorem`.

```lean
theorem Subgroup.exists_strict_continuous_section_refinement {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {K S H : Subgroup G} [IsClosed ↑K] [IsClosed ↑S] (hKS : K < S) (hSH : S ≤ H) {s : G ⧸ H → G ⧸ S} (hscont : Continuous s) (hsright : Function.RightInverse s (quotientMapOfLE hSH)) : ∃ (T : Subgroup G) (_ : K ≤ T) (hTS : T < S) (_ : IsClosed ↑T) (t : G ⧸ H → G ⧸ T), Continuous t ∧ Function.RightInverse t (quotientMapOfLE ⋯) ∧ s = quotientMapOfLE ⋯ ∘ t
```

**Native source docstring:** A continuous section through `G ⧸ S` can be strictly refined through an
intermediate closed subgroup whenever `K < S`.

[Source](../ProfiniteGroups/ContinuousSection.lean#L236) (native source start line; generated entries may point to their parent).

#### Subgroup.quotientMapOfLE_exists_continuous_section_of_isClosed

Kind: `theorem`.

```lean
theorem Subgroup.quotientMapOfLE_exists_continuous_section_of_isClosed {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {K H : Subgroup G} [IsClosed ↑K] [IsClosed ↑H] (hKH : K ≤ H) : ∃ (s : G ⧸ H → G ⧸ K), Continuous s ∧ Function.RightInverse s (quotientMapOfLE hKH)
```

**Native source docstring:** The projection between the left-coset spaces of two closed subgroups of a
profinite group has a continuous section.

[Source](../ProfiniteGroups/ContinuousSection.lean#L396) (native source start line; generated entries may point to their parent).

#### Native instance table

- `QuotientGroup.instTotallyDisconnectedSpace`: `TotallyDisconnectedSpace`; type names: `HasQuotient.Quotient`

### ProfiniteGroups.EpiMono

3 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.mono_iff_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.mono_iff_injective {G H : ProfiniteGrp.{u}} (f : G ⟶ H) : CategoryTheory.Mono f ↔ Function.Injective ⇑(Hom.hom f)
```

**Native source docstring:** A morphism of profinite groups is a monomorphism exactly when its underlying
function is injective.

[Source](../ProfiniteGroups/EpiMono.lean#L34) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.epi_iff_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.epi_iff_surjective {G H : ProfiniteGrp.{u}} (f : G ⟶ H) : CategoryTheory.Epi f ↔ Function.Surjective ⇑(Hom.hom f)
```

**Native source docstring:** A morphism of profinite groups is an epimorphism exactly when its underlying
function is surjective.

[Source](../ProfiniteGroups/EpiMono.lean#L106) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.mono_iff_injective

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.mono_iff_injective {G H : ProfiniteAddGrp.{u}} (f : G ⟶ H) : CategoryTheory.Mono f ↔ Function.Injective ⇑(Hom.hom f)
```

**Native source docstring:** A morphism of profinite additive groups is a monomorphism exactly when its
underlying function is injective.

[Source](../ProfiniteGroups/EpiMono.lean#L152) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.FinitePresentation

29 native named entries; 2 native instance-table rows.

#### Profinite.FinitePresentation.injectiveSourceStage

Kind: `def`.

```lean
def Profinite.FinitePresentation.injectiveSourceStage {X Y : Profinite} (f : X ⟶ Y) (B : DiscreteQuotient ↑Y.toTop) : DiscreteQuotient ↑X.toTop
```

**Native source docstring:** The source stage over a finite quotient of the target.

[Source](../ProfiniteGroups/FinitePresentation.lean#L36) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveStageMap

Kind: `def`.

```lean
def Profinite.FinitePresentation.injectiveStageMap {X Y : Profinite} (f : X ⟶ Y) (B : DiscreteQuotient ↑Y.toTop) : Quotient (injectiveSourceStage f B).toSetoid → Quotient B.toSetoid
```

**Native source docstring:** The map from a pulled-back source stage to its target stage.

[Source](../ProfiniteGroups/FinitePresentation.lean#L40) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveIndex

Kind: `def`.

```lean
def Profinite.FinitePresentation.injectiveIndex {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Functor (DiscreteQuotient ↑Y.toTop) (DiscreteQuotient ↑X.toTop)
```

**Native source docstring:** Pull finite target quotients back to finite source quotients.

[Source](../ProfiniteGroups/FinitePresentation.lean#L44) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveStageMap_injective

Kind: `theorem`.

```lean
theorem Profinite.FinitePresentation.injectiveStageMap_injective {X Y : Profinite} (f : X ⟶ Y) (B : DiscreteQuotient ↑Y.toTop) : Function.Injective (injectiveStageMap f B)
```

**Native source docstring:** A pulled-back finite stage maps injectively to its target stage.

[Source](../ProfiniteGroups/FinitePresentation.lean#L49) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveIndex_initial

Kind: `theorem`.

```lean
theorem Profinite.FinitePresentation.injectiveIndex_initial {X Y : Profinite} (f : X ⟶ Y) (hf : Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom f)) : (injectiveIndex f).Initial
```

**Native source docstring:** If `f` is injective, pulled-back target quotients are cofinal among the
finite quotients of the source.

[Source](../ProfiniteGroups/FinitePresentation.lean#L58) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveFintypeMap

Kind: `def`.

```lean
def Profinite.FinitePresentation.injectiveFintypeMap {X Y : Profinite} (f : X ⟶ Y) : (injectiveIndex f).comp X.fintypeDiagram ⟶ Y.fintypeDiagram
```

**Native source docstring:** The natural transformation of finite stages induced by an injective
profinite map. The definition makes sense without the injectivity hypothesis.

[Source](../ProfiniteGroups/FinitePresentation.lean#L95) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveSourceDiagram

Kind: `def`.

```lean
abbrev Profinite.FinitePresentation.injectiveSourceDiagram {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Functor (DiscreteQuotient ↑Y.toTop) Profinite
```

**Native source docstring:** The source profinite diagram indexed by finite target quotients.

[Source](../ProfiniteGroups/FinitePresentation.lean#L105) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveDiagramMap

Kind: `def`.

```lean
def Profinite.FinitePresentation.injectiveDiagramMap {X Y : Profinite} (f : X ⟶ Y) : injectiveSourceDiagram f ⟶ Y.diagram
```

**Native source docstring:** The natural transformation of finite discrete profinite stages induced by
`f`.

[Source](../ProfiniteGroups/FinitePresentation.lean#L109) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveSourceCone

Kind: `def`.

```lean
def Profinite.FinitePresentation.injectiveSourceCone {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Limits.Cone (injectiveSourceDiagram f)
```

**Native source docstring:** The source limit cone reindexed by finite target quotients.

[Source](../ProfiniteGroups/FinitePresentation.lean#L114) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveSourceLimit

Kind: `def`.

```lean
noncomputable def Profinite.FinitePresentation.injectiveSourceLimit {X Y : Profinite} (f : X ⟶ Y) (hf : Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom f)) : CategoryTheory.Limits.IsLimit (injectiveSourceCone f)
```

**Native source docstring:** The reindexed source cone is a limit cone when `f` is injective.

[Source](../ProfiniteGroups/FinitePresentation.lean#L118) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveFintypeMap_app_injective

Kind: `theorem`.

```lean
theorem Profinite.FinitePresentation.injectiveFintypeMap_app_injective {X Y : Profinite} (f : X ⟶ Y) (B : DiscreteQuotient ↑Y.toTop) : Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom ((injectiveFintypeMap f).app B))
```

**Native source docstring:** Every component of the finite-stage transformation for an injective map is
injective.

[Source](../ProfiniteGroups/FinitePresentation.lean#L124) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.injectiveConeHom

Kind: `def`.

```lean
def Profinite.FinitePresentation.injectiveConeHom {X Y : Profinite} (f : X ⟶ Y) : (CategoryTheory.Limits.Cone.postcompose (injectiveDiagramMap f)).obj (injectiveSourceCone f) ⟶ Y.asLimitCone
```

**Native source docstring:** The map of limit cones induced by the finite-stage transformation is the
original profinite map.

[Source](../ProfiniteGroups/FinitePresentation.lean#L130) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.SurjectiveIndex

Kind: `def`.

```lean
abbrev Profinite.FinitePresentation.SurjectiveIndex {X Y : Profinite} (f : X ⟶ Y) : Type u
```

**Native source docstring:** A common finite-stage index for a profinite map consists of a source
quotient refining the pullback of a target quotient. The target projection
composed with the map factors through the source projection.

[Source](../ProfiniteGroups/FinitePresentation.lean#L142) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveIndex_nonempty

Kind: `instance`.

```lean
instance Profinite.FinitePresentation.surjectiveIndex_nonempty {X Y : Profinite} (f : X ⟶ Y) : Nonempty (SurjectiveIndex f)
```

**Native source docstring:** The terminal source and target quotients provide a common stage for any map.

[Source](../ProfiniteGroups/FinitePresentation.lean#L148) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveIndex_isCodirected

Kind: `instance`.

```lean
instance Profinite.FinitePresentation.surjectiveIndex_isCodirected {X Y : Profinite} (f : X ⟶ Y) : IsCodirectedOrder (SurjectiveIndex f)
```

**Native source docstring:** Two finite source/target quotient pairs admit a common refinement,
providing the cofiltered index needed for the surjective presentation.

[Source](../ProfiniteGroups/FinitePresentation.lean#L154) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveSourceIndex

Kind: `def`.

```lean
def Profinite.FinitePresentation.surjectiveSourceIndex {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Functor (SurjectiveIndex f) (DiscreteQuotient ↑X.toTop)
```

**Native source docstring:** Project a common finite-stage index to its source quotient.

[Source](../ProfiniteGroups/FinitePresentation.lean#L164) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveTargetIndex

Kind: `def`.

```lean
def Profinite.FinitePresentation.surjectiveTargetIndex {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Functor (SurjectiveIndex f) (DiscreteQuotient ↑Y.toTop)
```

**Native source docstring:** Project a common finite-stage index to its target quotient.

[Source](../ProfiniteGroups/FinitePresentation.lean#L168) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveSourceIndex_initial

Kind: `theorem`.

```lean
theorem Profinite.FinitePresentation.surjectiveSourceIndex_initial {X Y : Profinite} (f : X ⟶ Y) : (surjectiveSourceIndex f).Initial
```

**Native source docstring:** The source projection from common finite stages is initial.

[Source](../ProfiniteGroups/FinitePresentation.lean#L172) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveTargetIndex_initial

Kind: `theorem`.

```lean
theorem Profinite.FinitePresentation.surjectiveTargetIndex_initial {X Y : Profinite} (f : X ⟶ Y) : (surjectiveTargetIndex f).Initial
```

**Native source docstring:** The target projection from common finite stages is initial.

[Source](../ProfiniteGroups/FinitePresentation.lean#L182) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveFintypeMap

Kind: `def`.

```lean
def Profinite.FinitePresentation.surjectiveFintypeMap {X Y : Profinite} (f : X ⟶ Y) : (surjectiveSourceIndex f).comp X.fintypeDiagram ⟶ (surjectiveTargetIndex f).comp Y.fintypeDiagram
```

**Native source docstring:** The natural transformation between the common finite source and target
stages.

[Source](../ProfiniteGroups/FinitePresentation.lean#L190) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveFintypeMap_app_surjective

Kind: `theorem`.

```lean
theorem Profinite.FinitePresentation.surjectiveFintypeMap_app_surjective {X Y : Profinite} (f : X ⟶ Y) (hf : Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom f)) (P : SurjectiveIndex f) : Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom ((surjectiveFintypeMap f).app P))
```

**Native source docstring:** Every component of the common finite-stage transformation is surjective
when the original profinite map is surjective.

[Source](../ProfiniteGroups/FinitePresentation.lean#L201) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveSourceDiagram

Kind: `def`.

```lean
abbrev Profinite.FinitePresentation.surjectiveSourceDiagram {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Functor (SurjectiveIndex f) Profinite
```

**Native source docstring:** The source profinite diagram over the common finite-stage index.

[Source](../ProfiniteGroups/FinitePresentation.lean#L210) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveTargetDiagram

Kind: `def`.

```lean
abbrev Profinite.FinitePresentation.surjectiveTargetDiagram {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Functor (SurjectiveIndex f) Profinite
```

**Native source docstring:** The target profinite diagram over the common finite-stage index.

[Source](../ProfiniteGroups/FinitePresentation.lean#L214) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveDiagramMap

Kind: `def`.

```lean
def Profinite.FinitePresentation.surjectiveDiagramMap {X Y : Profinite} (f : X ⟶ Y) : surjectiveSourceDiagram f ⟶ surjectiveTargetDiagram f
```

**Native source docstring:** The natural transformation of finite discrete profinite stages induced by
`f`.

[Source](../ProfiniteGroups/FinitePresentation.lean#L218) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveSourceCone

Kind: `def`.

```lean
def Profinite.FinitePresentation.surjectiveSourceCone {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Limits.Cone (surjectiveSourceDiagram f)
```

**Native source docstring:** The source limit cone over the common finite-stage index.

[Source](../ProfiniteGroups/FinitePresentation.lean#L223) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveTargetCone

Kind: `def`.

```lean
def Profinite.FinitePresentation.surjectiveTargetCone {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Limits.Cone (surjectiveTargetDiagram f)
```

**Native source docstring:** The target limit cone over the common finite-stage index.

[Source](../ProfiniteGroups/FinitePresentation.lean#L227) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveSourceLimit

Kind: `def`.

```lean
noncomputable def Profinite.FinitePresentation.surjectiveSourceLimit {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Limits.IsLimit (surjectiveSourceCone f)
```

**Native source docstring:** The common-index source cone is a limit cone.

[Source](../ProfiniteGroups/FinitePresentation.lean#L231) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveTargetLimit

Kind: `def`.

```lean
noncomputable def Profinite.FinitePresentation.surjectiveTargetLimit {X Y : Profinite} (f : X ⟶ Y) : CategoryTheory.Limits.IsLimit (surjectiveTargetCone f)
```

**Native source docstring:** The common-index target cone is a limit cone.

[Source](../ProfiniteGroups/FinitePresentation.lean#L238) (native source start line; generated entries may point to their parent).

#### Profinite.FinitePresentation.surjectiveConeHom

Kind: `def`.

```lean
def Profinite.FinitePresentation.surjectiveConeHom {X Y : Profinite} (f : X ⟶ Y) : (CategoryTheory.Limits.Cone.postcompose (surjectiveDiagramMap f)).obj (surjectiveSourceCone f) ⟶ surjectiveTargetCone f
```

**Native source docstring:** The map of common-index limit cones induced by the finite-stage
transformation is the original profinite map.

[Source](../ProfiniteGroups/FinitePresentation.lean#L245) (native source start line; generated entries may point to their parent).

#### Native instance table

- `Profinite.FinitePresentation.surjectiveIndex_isCodirected`: `IsDirected`; type names: `Profinite.FinitePresentation.SurjectiveIndex`

- `Profinite.FinitePresentation.surjectiveIndex_nonempty`: `Nonempty`; type names: `Profinite.FinitePresentation.SurjectiveIndex`

### ProfiniteGroups.FiniteQuotientHom

36 native named entries; 3 native instance-table rows.

#### ProfiniteGrp.FiniteQuotientHom.StageIndex

Kind: `def`.

```lean
abbrev ProfiniteGrp.FiniteQuotientHom.StageIndex (G : ProfiniteGrp.{u}) : Type u
```

**Native source docstring:** Open normal subgroups ordered by reverse inclusion, so passing to a
smaller subgroup gives a forward map in the quotient-homomorphism system.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L31) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.diagramObjDiscreteTopology

Kind: `instance`.

```lean
instance ProfiniteGrp.FiniteQuotientHom.diagramObjDiscreteTopology (H : ProfiniteGrp.{u}) (V : OpenNormalSubgroup ↑H.toProfinite.toTop) : DiscreteTopology ↑(H.diagram.obj V).toProfinite.toTop
```

**Native source docstring:** The finite quotient objects in `ProfiniteGrp.diagram` have their defining
discrete topology.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L36) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomStage

Kind: `def`.

```lean
abbrev ProfiniteGrp.FiniteQuotientHom.HomStage (G : ProfiniteGrp.{u}) (F : Type v) [Group F] (U : StageIndex G) : Type (max u v)
```

**Native source docstring:** Homomorphisms from the finite quotient at a given source stage.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L43) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.quotientTransition

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.quotientTransition {P : ProfiniteGrp.{u}} {V W : OpenNormalSubgroup ↑P.toProfinite.toTop} (h : V ≤ W) : ↑P.toProfinite.toTop ⧸ ↑V.toOpenSubgroup →* ↑P.toProfinite.toTop ⧸ ↑W.toOpenSubgroup
```

**Native source docstring:** The canonical transition between quotients by nested open normal
subgroups.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L48) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.quotientTransition_mk

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.quotientTransition_mk {P : ProfiniteGrp.{u}} {V W : OpenNormalSubgroup ↑P.toProfinite.toTop} (h : V ≤ W) (g : ↑P.toProfinite.toTop) : (quotientTransition h) ↑g = ↑g
```

**Native source docstring:** The quotient transition sends the class of an element to its class.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L55) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomStageHom

Kind: `structure`.

```lean
structure ProfiniteGrp.FiniteQuotientHom.HomStageHom (G : ProfiniteGrp.{u}) (F : Type v) [Group F] (U V : StageIndex G) : Type (max u v)
```

**Native source docstring:** A bundled function between quotient-homomorphism stages.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L62) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomStageHom.mk

Kind: `ctor`.

```lean
constructor ProfiniteGrp.FiniteQuotientHom.HomStageHom.mk : {G : ProfiniteGrp.{u}} → {F : Type v} → [inst : Group F] → {U V : ProfiniteGrp.FiniteQuotientHom.StageIndex G} → (ProfiniteGrp.FiniteQuotientHom.HomStage G F U → ProfiniteGrp.FiniteQuotientHom.HomStage G F V) → ProfiniteGrp.FiniteQuotientHom.HomStageHom G F U V
```

**Original catalogue explanation (not a Lean docstring):** Constructor packaging a function between two finite-quotient Hom stages.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L62) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomStageHom.toFun

Kind: `def`.

```lean
abbrev ProfiniteGrp.FiniteQuotientHom.HomStageHom.toFun {G : ProfiniteGrp.{u}} {F : Type v} [Group F] {U V : StageIndex G} (self : HomStageHom G F U V) : HomStage G F U → HomStage G F V
```

**Native source docstring:** The underlying function.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L66) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.instFunLikeHomStageHomHomStage

Kind: `instance`.

```lean
instance ProfiniteGrp.FiniteQuotientHom.instFunLikeHomStageHomHomStage (G : ProfiniteGrp.{u}) (F : Type v) [Group F] (U V : StageIndex G) : FunLike (HomStageHom G F U V) (HomStage G F U) (HomStage G F V)
```

**Original catalogue explanation (not a Lean docstring):** The stage-map bundle acts on stage homomorphisms as a function; equality of the underlying functions determines the bundle.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L68) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.homStageMap

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.homStageMap (G : ProfiniteGrp.{u}) (F : Type v) [Group F] (U V : StageIndex G) (h : U ≤ V) : HomStageHom G F U V
```

**Native source docstring:** Precomposition with a quotient transition gives the source-stage map.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L79) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.homStageDirectedSystem

Kind: `instance`.

```lean
instance ProfiniteGrp.FiniteQuotientHom.homStageDirectedSystem (G : ProfiniteGrp.{u}) (F : Type v) [Group F] : DirectedSystem (HomStage G F) fun (x1 x2 : StageIndex G) (x3 : x1 ≤ x2) => ⇑(homStageMap G F x1 x2 x3)
```

**Native source docstring:** Source-quotient transition maps form the directed system underlying the
filtered-colimit representation of continuous maps into a discrete group.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L85) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit

Kind: `def`.

```lean
abbrev ProfiniteGrp.FiniteQuotientHom.HomColimit (G : ProfiniteGrp.{u}) (F : Type v) [Group F] : Type (max u v)
```

**Native source docstring:** The filtered colimit of homomorphisms from finite quotients of `G` to
`F`.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L98) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.stageToContinuousHom

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.stageToContinuousHom (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] (U : StageIndex G) (a : HomStage G F U) : ↑G.toProfinite.toTop →ₜ* F
```

**Native source docstring:** A finite-stage homomorphism gives a continuous homomorphism from `G` to
any topologized group: the finite source quotient is discrete.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L103) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.stageToContinuousHom_compat

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.stageToContinuousHom_compat (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] (U V : StageIndex G) (h : U ≤ V) (a : HomStage G F U) : stageToContinuousHom G F U a = stageToContinuousHom G F V ((homStageMap G F U V h) a)
```

**Native source docstring:** The continuous homomorphisms induced by finite stages respect source-stage
transitions.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L114) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.stageToContinuousHom_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.stageToContinuousHom_injective (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] (U : StageIndex G) : Function.Injective (stageToContinuousHom G F U)
```

**Native source docstring:** A finite-stage homomorphism is determined by the continuous homomorphism
it induces on `G`.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L124) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] : HomColimit G F → ↑G.toProfinite.toTop →ₜ* F
```

**Native source docstring:** Interpret a filtered-colimit class as a continuous homomorphism.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L137) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom_mk

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom_mk (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] (U : StageIndex G) (a : HomStage G F U) : toContinuousHom G F ⟦⟨U, a⟩⟧ = stageToContinuousHom G F U a
```

**Native source docstring:** Interpret a representative from a specified finite stage.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L145) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom_injective (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] : Function.Injective (toContinuousHom G F)
```

**Native source docstring:** Interpretation of the finite-stage colimit is injective.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L154) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.kernelOpenNormal

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.kernelOpenNormal {G : ProfiniteGrp.{u}} {F : Type v} [Group F] [TopologicalSpace F] [DiscreteTopology F] (q : ↑G.toProfinite.toTop →ₜ* F) : OpenNormalSubgroup ↑G.toProfinite.toTop
```

**Native source docstring:** The open normal kernel of a continuous homomorphism into a discrete
group.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L164) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.kernelFiniteQuotientMap

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.kernelFiniteQuotientMap {G : ProfiniteGrp.{u}} {F : Type v} [Group F] [TopologicalSpace F] [DiscreteTopology F] (q : ↑G.toProfinite.toTop →ₜ* F) : ↑G.toProfinite.toTop ⧸ ↑(kernelOpenNormal q).toOpenSubgroup →* F
```

**Native source docstring:** The factorization through the finite quotient by an open kernel.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L176) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.ofContinuousHom

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.HomColimit.ofContinuousHom (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] [DiscreteTopology F] (q : ↑G.toProfinite.toTop →ₜ* F) : HomColimit G F
```

**Native source docstring:** Represent a continuous homomorphism by the quotient through its open
kernel.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L182) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom_ofContinuousHom

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom_ofContinuousHom (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] [DiscreteTopology F] (q : ↑G.toProfinite.toTop →ₜ* F) : toContinuousHom G F (ofContinuousHom G F q) = q
```

**Native source docstring:** Interpreting the representative through the open kernel recovers the
original continuous homomorphism.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L189) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.continuousHomEquiv

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.HomColimit.continuousHomEquiv (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] [DiscreteTopology F] : HomColimit G F ≃ (↑G.toProfinite.toTop →ₜ* F)
```

**Native source docstring:** Continuous homomorphisms to a discrete group are the filtered colimit of
homomorphisms from the finite quotients of the source.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L201) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.continuousHomEquiv_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomColimit.continuousHomEquiv_apply (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] [DiscreteTopology F] (x : HomColimit G F) : (continuousHomEquiv G F) x = toContinuousHom G F x
```

**Native source docstring:** The forward map of `HomColimit.continuousHomEquiv` is interpretation.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L215) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.continuousHomEquiv_symm_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomColimit.continuousHomEquiv_symm_apply (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] [DiscreteTopology F] (q : ↑G.toProfinite.toTop →ₜ* F) : (continuousHomEquiv G F).symm q = ofContinuousHom G F q
```

**Native source docstring:** The inverse of `HomColimit.continuousHomEquiv` uses the open kernel.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L225) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.postcomp

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.HomColimit.postcomp (G K L : ProfiniteGrp.{u}) [DiscreteTopology ↑L.toProfinite.toTop] (p : K ⟶ L) : HomColimit G ↑K.toProfinite.toTop → HomColimit G ↑L.toProfinite.toTop
```

**Native source docstring:** Postcomposition maps source-stage colimits covariantly into a discrete
profinite target. The intermediate target need not be discrete.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L235) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom_postcomp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom_postcomp (G K L : ProfiniteGrp.{u}) [DiscreteTopology ↑L.toProfinite.toTop] (p : K ⟶ L) (x : HomColimit G ↑K.toProfinite.toTop) : toContinuousHom G (↑L.toProfinite.toTop) (postcomp G K L p x) = (Hom.hom p).comp (toContinuousHom G (↑K.toProfinite.toTop) x)
```

**Native source docstring:** Interpretation commutes with postcomposition.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L243) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomLimit

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.HomLimit (G H : ProfiniteGrp.{u}) : Type u
```

**Native source docstring:** The compatible-family model of `lim_V colim_U Hom(G/U, H/V)`.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L253) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomLimit.cone

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.HomLimit.cone {G H : ProfiniteGrp.{u}} (x : HomLimit G H) : CategoryTheory.Limits.Cone H.diagram
```

**Native source docstring:** A compatible family defines a cone over the target's finite-quotient
diagram.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L259) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomLimit.toHom

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FiniteQuotientHom.HomLimit.toHom {G H : ProfiniteGrp.{u}} (x : HomLimit G H) : G ⟶ H
```

**Native source docstring:** Assemble a compatible finite-quotient family into a profinite-group
homomorphism.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L277) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomLimit.toHom_fac

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomLimit.toHom_fac {G H : ProfiniteGrp.{u}} (x : HomLimit G H) (V : OpenNormalSubgroup ↑H.toProfinite.toTop) : CategoryTheory.CategoryStruct.comp x.toHom (proj V) = x.cone.π.app V
```

**Native source docstring:** The assembled homomorphism induces the specified map at every finite
target quotient.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L283) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomLimit.toHom_fac_assoc

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomLimit.toHom_fac_assoc {G H : ProfiniteGrp.{u}} (x : HomLimit G H) (V : OpenNormalSubgroup ↑H.toProfinite.toTop) {Z : ProfiniteGrp.{u}} (h : H.diagram.obj V ⟶ Z) : CategoryTheory.CategoryStruct.comp x.toHom (CategoryTheory.CategoryStruct.comp (proj V) h) = CategoryTheory.CategoryStruct.comp (x.cone.π.app V) h
```

**Native source docstring:** The assembled homomorphism induces the specified map at every finite
target quotient.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L285) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomLimit.ofHom

Kind: `def`.

```lean
def ProfiniteGrp.FiniteQuotientHom.HomLimit.ofHom {G H : ProfiniteGrp.{u}} (f : G ⟶ H) : HomLimit G H
```

**Native source docstring:** A profinite-group homomorphism gives a compatible family on finite target
quotients.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L291) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomLimit.toHom_ofHom

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomLimit.toHom_ofHom {G H : ProfiniteGrp.{u}} (f : G ⟶ H) : (ofHom f).toHom = f
```

**Native source docstring:** Assembling the finite-quotient family of a homomorphism recovers it.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L303) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.HomLimit.ofHom_toHom

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FiniteQuotientHom.HomLimit.ofHom_toHom {G H : ProfiniteGrp.{u}} (x : HomLimit G H) : ofHom x.toHom = x
```

**Native source docstring:** Taking the finite-quotient family of an assembled family recovers that
family.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L319) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FiniteQuotientHom.homEquivHomLimit

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FiniteQuotientHom.homEquivHomLimit (G H : ProfiniteGrp.{u}) : (G ⟶ H) ≃ HomLimit G H
```

**Native source docstring:** The finite-quotient description of homomorphisms between profinite
groups: `Hom(G, H) ≃ lim_V colim_U Hom(G/U, H/V)`.

[Source](../ProfiniteGroups/FiniteQuotientHom.lean#L334) (native source start line; generated entries may point to their parent).

#### Native instance table

- `ProfiniteGrp.FiniteQuotientHom.diagramObjDiscreteTopology`: `DiscreteTopology`; type names: `TopCat.carrier`

- `ProfiniteGrp.FiniteQuotientHom.homStageDirectedSystem`: `DirectedSystem`; type names: `ProfiniteGrp.FiniteQuotientHom.HomStage`

- `ProfiniteGrp.FiniteQuotientHom.instFunLikeHomStageHomHomStage`: `DFunLike`; type names: `ProfiniteGrp.FiniteQuotientHom.HomStageHom`, `ProfiniteGrp.FiniteQuotientHom.HomStage`, `ProfiniteGrp.FiniteQuotientHom.HomStage`

### ProfiniteGroups.FreeProduct

47 native named entries; 3 native instance-table rows.

#### ProfiniteGrp.FreeProduct.Abstract

Kind: `def`.

```lean
abbrev ProfiniteGrp.FreeProduct.Abstract {ι : Type v} (G : ι → ProfiniteGrp.{u}) : Type (max u v)
```

**Native source docstring:** The abstract free product of the underlying groups.

[Source](../ProfiniteGroups/FreeProduct.lean#L46) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient

Kind: `structure`.

```lean
structure ProfiniteGrp.FreeProduct.AdmissibleQuotient {ι : Type v} (G : ι → ProfiniteGrp.{u}) extends FiniteIndexNormalSubgroup (ProfiniteGrp.FreeProduct.Abstract G) : Type (max u v)
```

**Native source docstring:** A finite quotient of the abstract free product is admissible when its
restriction to every profinite factor is continuous. Openness of the kernels
is the convenient finite-discrete formulation of this condition.

[Source](../ProfiniteGroups/FreeProduct.lean#L50) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.mk

Kind: `ctor`.

```lean
constructor ProfiniteGrp.FreeProduct.AdmissibleQuotient.mk : {ι : Type v} → {G : ι → ProfiniteGrp.{u}} → (toFiniteIndexNormalSubgroup : FiniteIndexNormalSubgroup (ProfiniteGrp.FreeProduct.Abstract G)) → (∀ (i : ι), IsOpen ↑(Subgroup.comap Monoid.CoprodI.of toFiniteIndexNormalSubgroup.toSubgroup)) → ProfiniteGrp.FreeProduct.AdmissibleQuotient G
```

**Original catalogue explanation (not a Lean docstring):** Constructor combining a finite-index normal subgroup with continuity of its pullback to each factor.

[Source](../ProfiniteGroups/FreeProduct.lean#L50) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.ext

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.AdmissibleQuotient.ext {ι : Type v} {G : ι → ProfiniteGrp.{u}} {x y : AdmissibleQuotient G} (carrier : x.carrier = y.carrier) : x = y
```

**Original catalogue explanation (not a Lean docstring):** Extensionality reduces equality of admissible quotients to their inherited subgroup field.

[Source](../ProfiniteGroups/FreeProduct.lean#L53) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.ext_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.AdmissibleQuotient.ext_iff {ι : Type v} {G : ι → ProfiniteGrp.{u}} {x y : AdmissibleQuotient G} : x = y ↔ x.carrier = y.carrier
```

**Original catalogue explanation (not a Lean docstring):** Two admissible quotients are equal exactly when their underlying finite-index normal subgroups agree.

[Source](../ProfiniteGroups/FreeProduct.lean#L53) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.toFiniteIndexNormalSubgroup

Kind: `def`.

```lean
abbrev ProfiniteGrp.FreeProduct.AdmissibleQuotient.toFiniteIndexNormalSubgroup {ι : Type v} {G : ι → ProfiniteGrp.{u}} (self : AdmissibleQuotient G) : FiniteIndexNormalSubgroup (Abstract G)
```

**Original catalogue explanation (not a Lean docstring):** Projection of an admissible quotient to its finite-index normal subgroup of the abstract free product.

[Source](../ProfiniteGroups/FreeProduct.lean#L54) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.isOpen_comap'

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.AdmissibleQuotient.isOpen_comap' {ι : Type v} {G : ι → ProfiniteGrp.{u}} (self : AdmissibleQuotient G) (i : ι) : IsOpen ↑(Subgroup.comap Monoid.CoprodI.of self.toSubgroup)
```

**Original catalogue explanation (not a Lean docstring):** An admissible quotient has an open inverse-image kernel in every profinite factor.

[Source](../ProfiniteGroups/FreeProduct.lean#L55) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.toFiniteIndexNormalSubgroup_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.AdmissibleQuotient.toFiniteIndexNormalSubgroup_injective {ι : Type v} (G : ι → ProfiniteGrp.{u}) : Function.Injective toFiniteIndexNormalSubgroup
```

**Native source docstring:** An admissible quotient is determined by its underlying finite-index normal
subgroup; the openness certificates introduce no additional choice of quotient.

[Source](../ProfiniteGroups/FreeProduct.lean#L62) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.instPartialOrder

Kind: `instance`.

```lean
instance ProfiniteGrp.FreeProduct.AdmissibleQuotient.instPartialOrder {ι : Type v} (G : ι → ProfiniteGrp.{u}) : PartialOrder (AdmissibleQuotient G)
```

**Original catalogue explanation (not a Lean docstring):** Orders admissible quotients through their finite-index normal subgroup order.

[Source](../ProfiniteGroups/FreeProduct.lean#L71) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.inf

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.AdmissibleQuotient.inf {ι : Type v} (G : ι → ProfiniteGrp.{u}) (U V : AdmissibleQuotient G) : AdmissibleQuotient G
```

**Native source docstring:** Common refinement of two finite admissible quotients. Intersecting their
kernels preserves openness after restriction to every profinite factor.

[Source](../ProfiniteGroups/FreeProduct.lean#L75) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.instSemilatticeInf

Kind: `instance`.

```lean
instance ProfiniteGrp.FreeProduct.AdmissibleQuotient.instSemilatticeInf {ι : Type v} (G : ι → ProfiniteGrp.{u}) : SemilatticeInf (AdmissibleQuotient G)
```

**Original catalogue explanation (not a Lean docstring):** Intersection of admissible quotient kernels supplies their common-refinement infimum.

[Source](../ProfiniteGroups/FreeProduct.lean#L90) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.top

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.AdmissibleQuotient.top {ι : Type v} (G : ι → ProfiniteGrp.{u}) : AdmissibleQuotient G
```

**Native source docstring:** The indiscrete quotient is admissible.

[Source](../ProfiniteGroups/FreeProduct.lean#L102) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.AdmissibleQuotient.instNonempty

Kind: `instance`.

```lean
instance ProfiniteGrp.FreeProduct.AdmissibleQuotient.instNonempty {ι : Type v} (G : ι → ProfiniteGrp.{u}) : Nonempty (AdmissibleQuotient G)
```

**Original catalogue explanation (not a Lean docstring):** The indiscrete admissible quotient witnesses nonemptiness of the quotient index category.

[Source](../ProfiniteGroups/FreeProduct.lean#L108) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.finiteGrpDiagram

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.finiteGrpDiagram {ι : Type v} (G : ι → ProfiniteGrp.{u}) : CategoryTheory.Functor (AdmissibleQuotient G) FiniteGrp.{max u v}
```

**Native source docstring:** The diagram of admissible finite quotients of the abstract free product.

[Source](../ProfiniteGroups/FreeProduct.lean#L112) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.diagram

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.diagram {ι : Type v} (G : ι → ProfiniteGrp.{u}) : CategoryTheory.Functor (AdmissibleQuotient G) ProfiniteGrp.{max u v}
```

**Native source docstring:** The admissible finite-quotient diagram viewed in profinite groups.

[Source](../ProfiniteGroups/FreeProduct.lean#L119) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.product

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.product {ι : Type v} (G : ι → ProfiniteGrp.{u}) : ProfiniteGrp.{max u v}
```

**Native source docstring:** The free profinite product, as the limit of its admissible finite
quotients.

[Source](../ProfiniteGroups/FreeProduct.lean#L123) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.etaFn

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.etaFn {ι : Type v} (G : ι → ProfiniteGrp.{u}) (x : Abstract G) : ↑(product G).toProfinite.toTop
```

**Native source docstring:** The canonical map from the abstract free product to the free profinite
product, as a function. Its range will be shown to be dense.

[Source](../ProfiniteGroups/FreeProduct.lean#L127) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.eta

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.eta {ι : Type v} (G : ι → ProfiniteGrp.{u}) : ↧(Abstract G) ⟶ ↧↑(product G).toProfinite.toTop
```

**Native source docstring:** The canonical homomorphism from the abstract free product to the
underlying group of the free profinite product.

[Source](../ProfiniteGroups/FreeProduct.lean#L132) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.denseRange

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.denseRange {ι : Type v} (G : ι → ProfiniteGrp.{u}) : DenseRange (etaFn G)
```

**Native source docstring:** The abstract free product has dense image in its admissible finite-quotient
completion.

[Source](../ProfiniteGroups/FreeProduct.lean#L141) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.of

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.of {ι : Type v} (G : ι → ProfiniteGrp.{u}) (i : ι) : ↑(G i).toProfinite.toTop →ₜ* ↑(product G).toProfinite.toTop
```

**Native source docstring:** The canonical continuous inclusion of a factor into the free profinite
product.

[Source](../ProfiniteGroups/FreeProduct.lean#L185) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.abstractLift

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.abstractLift {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) : Abstract G →* ↑P.toProfinite.toTop
```

**Native source docstring:** The abstract homomorphism out of the free product induced by a family of
continuous homomorphisms.

[Source](../ProfiniteGroups/FreeProduct.lean#L219) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.abstractLift_of

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.abstractLift_of {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (i : ι) (x : ↑(G i).toProfinite.toTop) : (abstractLift f) (Monoid.CoprodI.of x) = (f i) x
```

**Native source docstring:** An abstract lift agrees with its continuous input on each factor.

[Source](../ProfiniteGroups/FreeProduct.lean#L224) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.preimage

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.preimage {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (H : OpenNormalSubgroup ↑P.toProfinite.toTop) : AdmissibleQuotient G
```

**Native source docstring:** Pulling an open normal subgroup of the target back along the abstract
lift gives an admissible finite quotient.

[Source](../ProfiniteGroups/FreeProduct.lean#L230) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.preimage_le

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.preimage_le {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} {f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop} {H K : OpenNormalSubgroup ↑P.toProfinite.toTop} (h : H ≤ K) : preimage f H ≤ preimage f K
```

**Native source docstring:** Target quotient refinements induce source-side admissible refinements.

[Source](../ProfiniteGroups/FreeProduct.lean#L243) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.quotientMap

Kind: `def`.

```lean
def ProfiniteGrp.FreeProduct.quotientMap {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (H : OpenNormalSubgroup ↑P.toProfinite.toTop) : ↧(Abstract G ⧸ (preimage f H).toSubgroup) ⟶ ↧(↑P.toProfinite.toTop ⧸ ↑H.toOpenSubgroup)
```

**Native source docstring:** The finite quotient map induced by a family of continuous homomorphisms.

[Source](../ProfiniteGroups/FreeProduct.lean#L249) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.lift

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FreeProduct.lift {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) : product G ⟶ P
```

**Native source docstring:** The continuous homomorphism from the free profinite product induced by a
family of continuous homomorphisms.

[Source](../ProfiniteGroups/FreeProduct.lean#L256) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.lift_eta

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.lift_eta {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) : CategoryTheory.CategoryStruct.comp (eta G) ((CategoryTheory.forget₂ ProfiniteGrp.{max u v} GrpCat).map (lift f)) = GrpCat.ofHom (abstractLift f)
```

**Native source docstring:** On the dense abstract free product, the continuous universal lift agrees
with `abstractLift`. The equation is in groups after forgetting topology.

[Source](../ProfiniteGroups/FreeProduct.lean#L279) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.lift_eta_assoc

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.lift_eta_assoc {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) {Z : GrpCat} (h : (CategoryTheory.forget₂ ProfiniteGrp.{max u v} GrpCat).obj P ⟶ Z) : CategoryTheory.CategoryStruct.comp (eta G) (CategoryTheory.CategoryStruct.comp ((CategoryTheory.forget₂ ProfiniteGrp.{max u v} GrpCat).map (lift f)) h) = CategoryTheory.CategoryStruct.comp (GrpCat.ofHom (abstractLift f)) h
```

**Native source docstring:** On the dense abstract free product, the continuous universal lift agrees
with `abstractLift`. The equation is in groups after forgetting topology.

[Source](../ProfiniteGroups/FreeProduct.lean#L281) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.lift_unique

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.lift_unique {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f g : product G ⟶ P) (h : CategoryTheory.CategoryStruct.comp (eta G) ((CategoryTheory.forget₂ ProfiniteGrp.{max u v} GrpCat).map f) = CategoryTheory.CategoryStruct.comp (eta G) ((CategoryTheory.forget₂ ProfiniteGrp.{max u v} GrpCat).map g)) : f = g
```

**Native source docstring:** Two maps from the free profinite product that agree on the dense abstract
free product are equal.

[Source](../ProfiniteGroups/FreeProduct.lean#L292) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.lift_of

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.lift_of {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (i : ι) : (Hom.hom (lift f)).comp (of G i) = f i
```

**Native source docstring:** The free profinite universal lift restricts to each specified continuous
factor map; this is the computation rule for the universal construction.

[Source](../ProfiniteGroups/FreeProduct.lean#L304) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.of_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.of_injective {ι : Type v} (G : ι → ProfiniteGrp.{u}) (i : ι) : Function.Injective ⇑(of G i)
```

**Native source docstring:** Every factor embeds in the free profinite product.

[Source](../ProfiniteGroups/FreeProduct.lean#L354) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.factors_topologically_generate

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.factors_topologically_generate {ι : Type v} (G : ι → ProfiniteGrp.{u}) : (⨆ (i : ι), (of G i).range).topologicalClosure = ⊤
```

**Native source docstring:** The images of the factors topologically generate the free profinite
product.

[Source](../ProfiniteGroups/FreeProduct.lean#L364) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.hom_ext

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.hom_ext {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f g : product G ⟶ P) (h : ∀ (i : ι), (Hom.hom f).comp (of G i) = (Hom.hom g).comp (of G i)) : f = g
```

**Native source docstring:** Morphisms out of the free profinite product are determined by their
restrictions to the factors.

[Source](../ProfiniteGroups/FreeProduct.lean#L383) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.hom_ext_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.hom_ext_iff {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} {f g : product G ⟶ P} : f = g ↔ ∀ (i : ι), (Hom.hom f).comp (of G i) = (Hom.hom g).comp (of G i)
```

**Original catalogue explanation (not a Lean docstring):** Maps from the free profinite product agree exactly when they agree on every factor injection.

[Source](../ProfiniteGroups/FreeProduct.lean#L385) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.lift_comp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.lift_comp {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P Q : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (g : P ⟶ Q) : CategoryTheory.CategoryStruct.comp (lift f) g = lift fun (i : ι) => (Hom.hom g).comp (f i)
```

**Native source docstring:** The universal lift is natural in the profinite target.

[Source](../ProfiniteGroups/FreeProduct.lean#L397) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.lift_comp_assoc

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.lift_comp_assoc {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P Q : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (g : P ⟶ Q) {Z : ProfiniteGrp.{max u v}} (h : Q ⟶ Z) : CategoryTheory.CategoryStruct.comp (lift f) (CategoryTheory.CategoryStruct.comp g h) = CategoryTheory.CategoryStruct.comp (lift fun (i : ι) => (Hom.hom g).comp (f i)) h
```

**Native source docstring:** The universal lift is natural in the profinite target.

[Source](../ProfiniteGroups/FreeProduct.lean#L398) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.homEquiv

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FreeProduct.homEquiv {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} : (product G ⟶ P) ≃ ((i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop)
```

**Native source docstring:** Continuous homomorphisms out of the free profinite product are equivalent
to families of continuous homomorphisms out of its factors.

[Source](../ProfiniteGroups/FreeProduct.lean#L407) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.homEquiv_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.homEquiv_apply {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : product G ⟶ P) (i : ι) : homEquiv f i = (Hom.hom f).comp (of G i)
```

**Native source docstring:** The forward universal-property correspondence restricts a morphism to
the indicated factor via its canonical continuous map.

[Source](../ProfiniteGroups/FreeProduct.lean#L418) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.homEquiv_symm_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.homEquiv_symm_apply {ι : Type v} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) : homEquiv.symm f = lift f
```

**Native source docstring:** The inverse universal-property correspondence extends the supplied family
by the continuous universal lift.

[Source](../ProfiniteGroups/FreeProduct.lean#L424) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.emptyIsInitial

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FreeProduct.emptyIsInitial {ι : Type v} (G : ι → ProfiniteGrp.{u}) [IsEmpty ι] : CategoryTheory.Limits.IsInitial (product G)
```

**Native source docstring:** The free profinite product of an empty family is initial.

[Source](../ProfiniteGroups/FreeProduct.lean#L430) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.punitIso

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FreeProduct.punitIso (P : ProfiniteGrp.{u}) : (product fun (x : PUnit.{u + 1}) => P) ≅ P
```

**Native source docstring:** The free profinite product of a singleton family is its unique factor.

[Source](../ProfiniteGroups/FreeProduct.lean#L438) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.reindexIso

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FreeProduct.reindexIso {ι κ : Type v} (G : ι → ProfiniteGrp.{u}) (e : κ ≃ ι) : (product fun (k : κ) => G (e k)) ≅ product G
```

**Native source docstring:** Reindexing a family along an equivalence does not change its free
profinite product.

[Source](../ProfiniteGroups/FreeProduct.lean#L463) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.reindexIso_hom_of

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.reindexIso_hom_of {ι : Type v} {G : ι → ProfiniteGrp.{u}} {κ : Type v} (e : κ ≃ ι) (k : κ) : (Hom.hom (reindexIso G e).hom).comp (of (fun (k : κ) => G (e k)) k) = of G (e k)
```

**Native source docstring:** Reindexing by an equivalence carries the new factor inclusion to the
corresponding original factor inclusion.

[Source](../ProfiniteGroups/FreeProduct.lean#L504) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.map

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FreeProduct.map {ι : Type v} (G : ι → ProfiniteGrp.{u}) {H : ι → ProfiniteGrp.{u}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑(H i).toProfinite.toTop) : product G ⟶ product H
```

**Native source docstring:** A family of continuous homomorphisms induces a homomorphism of free
profinite products.

[Source](../ProfiniteGroups/FreeProduct.lean#L514) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.map_of

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.map_of {ι : Type v} (G : ι → ProfiniteGrp.{u}) {H : ι → ProfiniteGrp.{u}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑(H i).toProfinite.toTop) (i : ι) : (Hom.hom (map G f)).comp (of G i) = (of H i).comp (f i)
```

**Native source docstring:** The map induced by a family of homomorphisms agrees with that family on
each factor, followed by the target's canonical factor map.

[Source](../ProfiniteGroups/FreeProduct.lean#L519) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.map_id

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.map_id {ι : Type v} (G : ι → ProfiniteGrp.{u}) : (map G fun (i : ι) => ContinuousMonoidHom.id ↑(G i).toProfinite.toTop) = CategoryTheory.CategoryStruct.id (product G)
```

**Native source docstring:** Identity maps on the factors induce the identity on the free profinite
product, without unfolding its finite-quotient construction.

[Source](../ProfiniteGroups/FreeProduct.lean#L526) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProduct.map_comp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProduct.map_comp {ι : Type v} (G : ι → ProfiniteGrp.{u}) {H K : ι → ProfiniteGrp.{u}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑(H i).toProfinite.toTop) (g : (i : ι) → ↑(H i).toProfinite.toTop →ₜ* ↑(K i).toProfinite.toTop) : CategoryTheory.CategoryStruct.comp (map G f) (map H g) = map G fun (i : ι) => (g i).comp (f i)
```

**Native source docstring:** Mapping the factors twice agrees with mapping their componentwise
composites; categorical composition applies the left-hand map first.

[Source](../ProfiniteGroups/FreeProduct.lean#L536) (native source start line; generated entries may point to their parent).

#### Native instance table

- `ProfiniteGrp.FreeProduct.AdmissibleQuotient.instNonempty`: `Nonempty`; type names: `ProfiniteGrp.FreeProduct.AdmissibleQuotient`

- `ProfiniteGrp.FreeProduct.AdmissibleQuotient.instPartialOrder`: `PartialOrder`; type names: `ProfiniteGrp.FreeProduct.AdmissibleQuotient`

- `ProfiniteGrp.FreeProduct.AdmissibleQuotient.instSemilatticeInf`: `SemilatticeInf`; type names: `ProfiniteGrp.FreeProduct.AdmissibleQuotient`

### ProfiniteGroups.PiIdealQuotient

13 native named entries; 0 native instance-table rows.

#### Ideal.piQuotientMap

Kind: `def`.

```lean
def Ideal.piQuotientMap {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] (I : (i : ι) → Ideal (R i)) : ((i : ι) → R i) →+* (i : ι) → R i ⧸ I i
```

**Native source docstring:** The coordinate quotient homomorphism from a dependent product of rings to
the product of the coordinate quotients.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L29) (native source start line; generated entries may point to their parent).

#### Ideal.piQuotientMap_apply

Kind: `theorem`.

```lean
theorem Ideal.piQuotientMap_apply {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] (I : (i : ι) → Ideal (R i)) (x : (i : ι) → R i) (i : ι) : (piQuotientMap I) x i = (Quotient.mk (I i)) (x i)
```

**Native source docstring:** The coordinate quotient map acts pointwise.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L36) (native source start line; generated entries may point to their parent).

#### Ideal.piQuotientMap_surjective

Kind: `theorem`.

```lean
theorem Ideal.piQuotientMap_surjective {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] (I : (i : ι) → Ideal (R i)) : Function.Surjective ⇑(piQuotientMap I)
```

**Native source docstring:** The coordinate quotient map is surjective, including for an empty index
type.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L44) (native source start line; generated entries may point to their parent).

#### Ideal.ker_piQuotientMap

Kind: `theorem`.

```lean
theorem Ideal.ker_piQuotientMap {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] (I : (i : ι) → Ideal (R i)) : RingHom.ker (piQuotientMap I) = pi I
```

**Native source docstring:** The kernel of the coordinate quotient map is the product ideal.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L53) (native source start line; generated entries may point to their parent).

#### Ideal.piQuotientRingEquiv

Kind: `def`.

```lean
noncomputable def Ideal.piQuotientRingEquiv {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] (I : (i : ι) → Ideal (R i)) : ((i : ι) → R i) ⧸ pi I ≃+* ((i : ι) → R i ⧸ I i)
```

**Native source docstring:** Quotienting a dependent product by a product ideal is canonically
equivalent to the dependent product of the coordinate quotients.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L66) (native source start line; generated entries may point to their parent).

#### Ideal.piQuotientRingEquiv_mk_apply

Kind: `theorem`.

```lean
theorem Ideal.piQuotientRingEquiv_mk_apply {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] (I : (i : ι) → Ideal (R i)) (x : (i : ι) → R i) (i : ι) : (piQuotientRingEquiv I) ((Quotient.mk (pi I)) x) i = (Quotient.mk (I i)) (x i)
```

**Native source docstring:** The canonical product-quotient ring equivalence sends a quotient class to
the tuple of its coordinate quotient classes.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L75) (native source start line; generated entries may point to their parent).

#### Ideal.piQuotientRingEquiv_mk

Kind: `theorem`.

```lean
theorem Ideal.piQuotientRingEquiv_mk {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] (I : (i : ι) → Ideal (R i)) (x : (i : ι) → R i) : (piQuotientRingEquiv I) ((Quotient.mk (pi I)) x) = fun (i : ι) => (Quotient.mk (I i)) (x i)
```

**Native source docstring:** The underlying map of the canonical product-quotient ring equivalence is
induced by the coordinate quotient homomorphism.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L85) (native source start line; generated entries may point to their parent).

#### Ideal.isOpenQuotientMap_piQuotientMap

Kind: `theorem`.

```lean
theorem Ideal.isOpenQuotientMap_piQuotientMap {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] [(i : ι) → TopologicalSpace (R i)] [∀ (i : ι), IsTopologicalRing (R i)] (I : (i : ι) → Ideal (R i)) : IsOpenQuotientMap ⇑(piQuotientMap I)
```

**Native source docstring:** The product map of the coordinate quotient maps is an open quotient map.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L96) (native source start line; generated entries may point to their parent).

#### Ideal.continuous_piQuotientRingEquiv

Kind: `theorem`.

```lean
theorem Ideal.continuous_piQuotientRingEquiv {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] [(i : ι) → TopologicalSpace (R i)] [∀ (i : ι), IsTopologicalRing (R i)] (I : (i : ι) → Ideal (R i)) : Continuous ⇑(piQuotientRingEquiv I)
```

**Native source docstring:** The canonical product-quotient ring equivalence is continuous.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L106) (native source start line; generated entries may point to their parent).

#### Ideal.continuous_piQuotientRingEquiv_symm

Kind: `theorem`.

```lean
theorem Ideal.continuous_piQuotientRingEquiv_symm {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] [(i : ι) → TopologicalSpace (R i)] [∀ (i : ι), IsTopologicalRing (R i)] (I : (i : ι) → Ideal (R i)) : Continuous ⇑(piQuotientRingEquiv I).symm
```

**Native source docstring:** The inverse of the canonical product-quotient ring equivalence is
continuous.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L121) (native source start line; generated entries may point to their parent).

#### Ideal.piQuotientContinuousAddEquiv

Kind: `def`.

```lean
noncomputable def Ideal.piQuotientContinuousAddEquiv {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] [(i : ι) → TopologicalSpace (R i)] [∀ (i : ι), IsTopologicalRing (R i)] (I : (i : ι) → Ideal (R i)) : ((i : ι) → R i) ⧸ pi I ≃ₜ+ ((i : ι) → R i ⧸ I i)
```

**Native source docstring:** The topological form of the canonical product-ideal quotient
equivalence.  Its underlying additive equivalence is the one induced by
`piQuotientRingEquiv`.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L145) (native source start line; generated entries may point to their parent).

#### Ideal.piQuotientContinuousAddEquiv_apply

Kind: `theorem`.

```lean
theorem Ideal.piQuotientContinuousAddEquiv_apply {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] [(i : ι) → TopologicalSpace (R i)] [∀ (i : ι), IsTopologicalRing (R i)] (I : (i : ι) → Ideal (R i)) (x : ((i : ι) → R i) ⧸ pi I) : (piQuotientContinuousAddEquiv I) x = (piQuotientRingEquiv I) x
```

**Native source docstring:** The continuous additive and ring equivalences have the same underlying
map.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L157) (native source start line; generated entries may point to their parent).

#### Ideal.piQuotientContinuousAddEquiv_mk_apply

Kind: `theorem`.

```lean
theorem Ideal.piQuotientContinuousAddEquiv_mk_apply {ι : Type u} {R : ι → Type v} [(i : ι) → CommRing (R i)] [(i : ι) → TopologicalSpace (R i)] [∀ (i : ι), IsTopologicalRing (R i)] (I : (i : ι) → Ideal (R i)) (x : (i : ι) → R i) (i : ι) : (piQuotientContinuousAddEquiv I) ((Quotient.mk (pi I)) x) i = (Quotient.mk (I i)) (x i)
```

**Native source docstring:** Quotient representatives are sent coordinatewise by the continuous
additive equivalence.

[Source](../ProfiniteGroups/PiIdealQuotient.lean#L167) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.PrimewisePadic

18 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.instFactPrimeValNat_profiniteGroups

Kind: `theorem`.

```lean
theorem ProfiniteGrp.instFactPrimeValNat_profiniteGroups (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L37) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.padicFactor

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.padicFactor (p : Nat.Primes) : ProfiniteGrp.{u}
```

**Native source docstring:** The additive group of `p`-adic integers, written multiplicatively as a
profinite group in an arbitrary universe.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L39) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadic

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadic : ProfiniteGrp.{u}
```

**Native source docstring:** The product of the additive groups of the `p`-adic integers over all
primes, written multiplicatively.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L48) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicDiagonal

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicDiagonal (n : ℤ) : ↑primewisePadic.toProfinite.toTop
```

**Native source docstring:** The integral diagonal in the primewise p-adic product.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L53) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicDiagonal_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicDiagonal_apply (n : ℤ) (p : Nat.Primes) : primewisePadicDiagonal n p = Multiplicative.ofAdd { down := ↑n }
```

**Native source docstring:** The coordinates of the integral diagonal are the corresponding casts into
the p-adic integers.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L60) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicGenerator

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicGenerator : ↑primewisePadic.toProfinite.toTop
```

**Native source docstring:** The primewise element whose coordinate at every prime is `1`.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L68) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicGenerator_zpow

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicGenerator_zpow (n : ℤ) (p : Nat.Primes) : (primewisePadicGenerator ^ n) p = Multiplicative.ofAdd { down := ↑n }
```

**Native source docstring:** Integral powers of the canonical generator are the integral diagonal.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L72) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.denseRange_primewisePadicDiagonal

Kind: `theorem`.

```lean
theorem ProfiniteGrp.denseRange_primewisePadicDiagonal : DenseRange primewisePadicDiagonal
```

**Native source docstring:** The integral diagonal is dense in the product of all p-adic additive
groups.  Only finitely many coordinates occur in a basic product-open set, and
the Chinese remainder theorem simultaneously meets their p-power
congruences.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L83) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicGenerator_isTopologicalGenerator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicGenerator_isTopologicalGenerator : primewisePadic.IsTopologicalGenerator primewisePadicGenerator
```

**Native source docstring:** The canonical element topologically generates the primewise p-adic
product.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L145) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadic_isProcyclic

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadic_isProcyclic : primewisePadic.IsProcyclic
```

**Native source docstring:** The primewise p-adic product is procyclic.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L157) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionToPrimewisePadic

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.integerCompletionToPrimewisePadic : integerCompletion ⟶ primewisePadic
```

**Native source docstring:** The canonical map from the profinite completion of the integers to the
primewise p-adic product.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L161) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionToPrimewisePadic_eta_int

Kind: `theorem`.

```lean
theorem ProfiniteGrp.integerCompletionToPrimewisePadic_eta_int (n : ℤ) : (Hom.hom integerCompletionToPrimewisePadic) (ProfiniteCompletion.etaFn ↧(ULift.{u, 0} (Multiplicative ℤ)) { down := Multiplicative.ofAdd n }) = primewisePadicDiagonal n
```

**Native source docstring:** The canonical completion map restricts to the integral diagonal.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L167) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionToPrimewisePadic_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.integerCompletionToPrimewisePadic_surjective : Function.Surjective ⇑(Hom.hom integerCompletionToPrimewisePadic)
```

**Native source docstring:** The canonical map from the profinite completion onto the primewise p-adic
product is surjective.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L179) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionToPrimewisePadic_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.integerCompletionToPrimewisePadic_injective : Function.Injective ⇑(Hom.hom integerCompletionToPrimewisePadic)
```

**Native source docstring:** The canonical map from the profinite completion of the integers to the
primewise p-adic product is injective.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L486) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionEquivPrimewisePadic

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.integerCompletionEquivPrimewisePadic : ↑integerCompletion.toProfinite.toTop ≃ₜ* ↑primewisePadic.toProfinite.toTop
```

**Native source docstring:** The canonical continuous multiplicative equivalence from the profinite
completion of the integers to the product of the additive p-adic integers.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L495) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionEquivPrimewisePadic_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.integerCompletionEquivPrimewisePadic_apply (x : ↑integerCompletion.toProfinite.toTop) : integerCompletionEquivPrimewisePadic x = (Hom.hom integerCompletionToPrimewisePadic) x
```

**Native source docstring:** The canonical equivalence has the canonical completion morphism as its
underlying map.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L507) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionEquivPrimewisePadic_eta_int

Kind: `theorem`.

```lean
theorem ProfiniteGrp.integerCompletionEquivPrimewisePadic_eta_int (n : ℤ) : integerCompletionEquivPrimewisePadic (ProfiniteCompletion.etaFn ↧(ULift.{u, 0} (Multiplicative ℤ)) { down := Multiplicative.ofAdd n }) = primewisePadicDiagonal n
```

**Native source docstring:** The canonical equivalence restricts to the integral diagonal.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L516) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionEquivPrimewisePadic_symm_diagonal

Kind: `theorem`.

```lean
theorem ProfiniteGrp.integerCompletionEquivPrimewisePadic_symm_diagonal (n : ℤ) : integerCompletionEquivPrimewisePadic.symm (primewisePadicDiagonal n) = ProfiniteCompletion.etaFn ↧(ULift.{u, 0} (Multiplicative ℤ)) { down := Multiplicative.ofAdd n }
```

**Native source docstring:** The inverse of the canonical equivalence takes the integral diagonal to
the corresponding element of the profinite completion.

[Source](../ProfiniteGroups/PrimewisePadic.lean#L526) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.PrimewisePadicIdealTransport

20 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.instFactPrimeValNat_profiniteGroups_3

Kind: `theorem`.

```lean
theorem ProfiniteGrp.instFactPrimeValNat_profiniteGroups_3 (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L25) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicChangeUniverseRingEquiv

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicChangeUniverseRingEquiv (p : Nat.Primes) : ULift.{u, 0} ℤ_[↑p] ≃+* ULift.{v, 0} ℤ_[↑p]
```

**Native source docstring:** Change only the `ULift` universe of a p-adic factor.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L27) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicChangeUniverseRingEquiv_down

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicChangeUniverseRingEquiv_down (p : Nat.Primes) (x : ULift.{u, 0} ℤ_[↑p]) : ((liftedPadicChangeUniverseRingEquiv p) x).down = x.down
```

**Native source docstring:** Changing universes preserves the underlying p-adic integer.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L32) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicChangeUniverseRingEquiv_self

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicChangeUniverseRingEquiv_self (p : Nat.Primes) : liftedPadicChangeUniverseRingEquiv p = RingEquiv.refl (ULift.{u, 0} ℤ_[↑p])
```

**Native source docstring:** Changing a factor's universe to itself is the identity.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L39) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicChangeUniverseRingEquiv_symm

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicChangeUniverseRingEquiv_symm (p : Nat.Primes) : (liftedPadicChangeUniverseRingEquiv p).symm = liftedPadicChangeUniverseRingEquiv p
```

**Native source docstring:** Reversing the change of universe exchanges its endpoints.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L47) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicChangeUniverseRingEquiv_trans

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicChangeUniverseRingEquiv_trans (p : Nat.Primes) : (liftedPadicChangeUniverseRingEquiv p).trans (liftedPadicChangeUniverseRingEquiv p) = liftedPadicChangeUniverseRingEquiv p
```

**Native source docstring:** Successive factor universe changes compose directly.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L56) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRingChangeUniverse

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicRingChangeUniverse : primewisePadicRing ≃+* primewisePadicRing
```

**Native source docstring:** Change the universe of each factor of the primewise p-adic product ring.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L66) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRingChangeUniverse_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRingChangeUniverse_apply (x : primewisePadicRing) (p : Nat.Primes) : primewisePadicRingChangeUniverse x p = (liftedPadicChangeUniverseRingEquiv p) (x p)
```

**Native source docstring:** The product equivalence acts by the factor equivalence at each prime.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L71) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRingChangeUniverse_down

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRingChangeUniverse_down (x : primewisePadicRing) (p : Nat.Primes) : (primewisePadicRingChangeUniverse x p).down = (x p).down
```

**Native source docstring:** Each coordinate retains its underlying p-adic integer.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L79) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRingChangeUniverse_intCast

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRingChangeUniverse_intCast (n : ℤ) : primewisePadicRingChangeUniverse ↑n = ↑n
```

**Native source docstring:** The product ring equivalence preserves the integral diagonal.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L86) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRingChangeUniverse_self

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRingChangeUniverse_self : primewisePadicRingChangeUniverse = RingEquiv.refl primewisePadicRing
```

**Native source docstring:** Changing the product ring's universe to itself is the identity.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L92) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRingChangeUniverse_symm

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRingChangeUniverse_symm : primewisePadicRingChangeUniverse.symm = primewisePadicRingChangeUniverse
```

**Native source docstring:** Reversing the product equivalence exchanges its universe endpoints.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L98) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRingChangeUniverse_trans

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRingChangeUniverse_trans : primewisePadicRingChangeUniverse.trans primewisePadicRingChangeUniverse = primewisePadicRingChangeUniverse
```

**Native source docstring:** Successive changes of product universe compose directly.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L105) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealExponent_comap_changeUniverse

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicIdealExponent_comap_changeUniverse (p : Nat.Primes) (I : Ideal (ULift.{v, 0} ℤ_[↑p])) : liftedPadicIdealExponent p (Ideal.comap (liftedPadicChangeUniverseRingEquiv p) I) = liftedPadicIdealExponent p I
```

**Native source docstring:** Every factor ideal has the same exponent after changing its `ULift` universe.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L113) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealExponent_map_changeUniverse

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicIdealExponent_map_changeUniverse (p : Nat.Primes) (I : Ideal (ULift.{u, 0} ℤ_[↑p])) : liftedPadicIdealExponent p (Ideal.map (liftedPadicChangeUniverseRingEquiv p) I) = liftedPadicIdealExponent p I
```

**Native source docstring:** The equivalent forward image also preserves a factor ideal's exponent.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L138) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealOfExponent_comap_changeUniverse

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicIdealOfExponent_comap_changeUniverse (p : Nat.Primes) (n : ℕ∞) : Ideal.comap (liftedPadicChangeUniverseRingEquiv p) (liftedPadicIdealOfExponent p n) = liftedPadicIdealOfExponent p n
```

**Native source docstring:** Forming an uplifted factor ideal commutes with coordinate-preserving comap.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L149) (native source start line; generated entries may point to their parent).

#### Ideal.map_evalRingHom_comap_piCongrRight

Kind: `theorem`.

```lean
theorem Ideal.map_evalRingHom_comap_piCongrRight {ι : Type u_1} {R : ι → Type u_2} {S : ι → Type u_3} [(i : ι) → Semiring (R i)] [(i : ι) → Semiring (S i)] (e : (i : ι) → R i ≃+* S i) (I : Ideal ((i : ι) → S i)) (i : ι) : map (Pi.evalRingHom R i) (comap (RingEquiv.piCongrRight e) I) = comap (e i) (map (Pi.evalRingHom S i) I)
```

**Native source docstring:** Evaluation of the coordinate image commutes with comap of a
coordinatewise ring equivalence, without a closedness assumption.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L170) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealExponents_comap_changeUniverse

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicIdealExponents_comap_changeUniverse (I : Ideal primewisePadicRing) : primewisePadicIdealExponents (Ideal.comap primewisePadicRingChangeUniverse I) = primewisePadicIdealExponents I
```

**Native source docstring:** Every ideal in the product has universe-independent coordinate exponents;
closedness is not required because only coordinate images are compared.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L194) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealExponents_map_changeUniverse

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicIdealExponents_map_changeUniverse (I : Ideal primewisePadicRing) : primewisePadicIdealExponents (Ideal.map primewisePadicRingChangeUniverse I) = primewisePadicIdealExponents I
```

**Native source docstring:** The forward image of an arbitrary product ideal has the same exponents.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L207) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealOfExponents_comap_changeUniverse

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicIdealOfExponents_comap_changeUniverse (e : Nat.Primes → ℕ∞) : Ideal.comap primewisePadicRingChangeUniverse (primewisePadicIdealOfExponents e) = primewisePadicIdealOfExponents e
```

**Native source docstring:** The product ideal made from exponents commutes with changing universes.

[Source](../ProfiniteGroups/PrimewisePadicIdealTransport.lean#L218) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.PrimewisePadicIdeals

20 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.instFactPrimeValNat_profiniteGroups_2

Kind: `theorem`.

```lean
theorem ProfiniteGrp.instFactPrimeValNat_profiniteGroups_2 (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L34) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealOrderIso

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicIdealOrderIso (p : Nat.Primes) : Ideal (ULift.{u, 0} ℤ_[↑p]) ≃o ℕ∞ᵒᵈ
```

**Native source docstring:** Ideals in an uplifted p-adic factor, ordered by inclusion, correspond to
extended natural exponents in the reverse order.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L36) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealExponent

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicIdealExponent (p : Nat.Primes) (I : Ideal (ULift.{u, 0} ℤ_[↑p])) : ℕ∞
```

**Native source docstring:** The ordinary `ℕ∞` exponent of an ideal in an uplifted p-adic factor.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L43) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealOfExponent

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicIdealOfExponent (p : Nat.Primes) (n : ℕ∞) : Ideal (ULift.{u, 0} ℤ_[↑p])
```

**Native source docstring:** The ideal in an uplifted p-adic factor having the prescribed exponent.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L48) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealExponent_idealOfExponent

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicIdealExponent_idealOfExponent (p : Nat.Primes) (n : ℕ∞) : liftedPadicIdealExponent p (liftedPadicIdealOfExponent p n) = n
```

**Native source docstring:** Recovering the exponent of the ideal constructed from it.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L53) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealOfExponent_exponent

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicIdealOfExponent_exponent (p : Nat.Primes) (I : Ideal (ULift.{u, 0} ℤ_[↑p])) : liftedPadicIdealOfExponent p (liftedPadicIdealExponent p I) = I
```

**Native source docstring:** Reconstructing an uplifted p-adic ideal from its exponent.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L60) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealOfExponent_natCast

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicIdealOfExponent_natCast (p : Nat.Primes) (n : ℕ) : liftedPadicIdealOfExponent p ↑n = Ideal.comap ULift.ringEquiv (IsLocalRing.maximalIdeal ℤ_[↑p] ^ n)
```

**Native source docstring:** A finite exponent gives the corresponding power of the maximal ideal,
transported along the `ULift` ring equivalence.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L67) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealOfExponent_zero

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicIdealOfExponent_zero (p : Nat.Primes) : liftedPadicIdealOfExponent p 0 = ⊤
```

**Native source docstring:** Exponent zero gives the unit ideal.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L77) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicIdealOfExponent_top

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicIdealOfExponent_top (p : Nat.Primes) : liftedPadicIdealOfExponent p ⊤ = ⊥
```

**Native source docstring:** Infinite exponent gives the zero ideal.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L83) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isClosed_liftedPadicIdeal

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isClosed_liftedPadicIdeal (p : Nat.Primes) (I : Ideal (ULift.{u, 0} ℤ_[↑p])) : IsClosed ↑I
```

**Native source docstring:** Every ideal in an uplifted p-adic factor is closed.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L90) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealExponents

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicIdealExponents (I : Ideal primewisePadicRing) (p : Nat.Primes) : ℕ∞
```

**Native source docstring:** The coordinatewise exponents of an ideal in the primewise p-adic ring.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L103) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealOfExponents

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicIdealOfExponents (e : Nat.Primes → ℕ∞) : Ideal primewisePadicRing
```

**Native source docstring:** The product ideal having the prescribed primewise exponents.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L110) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.mem_primewisePadicIdealOfExponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.mem_primewisePadicIdealOfExponents (e : Nat.Primes → ℕ∞) (x : primewisePadicRing) : x ∈ primewisePadicIdealOfExponents e ↔ ∀ (p : Nat.Primes), x p ∈ liftedPadicIdealOfExponent p (e p)
```

**Native source docstring:** Membership in the ideal constructed from primewise exponents is
coordinatewise membership in the corresponding factor ideals.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L115) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isClosed_primewisePadicIdealOfExponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isClosed_primewisePadicIdealOfExponents (e : Nat.Primes → ℕ∞) : IsClosed ↑(primewisePadicIdealOfExponents e)
```

**Native source docstring:** A product ideal constructed from primewise exponents is closed.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L124) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.eq_primewisePadicIdealOfExponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.eq_primewisePadicIdealOfExponents (I : Ideal primewisePadicRing) (hI : IsClosed ↑I) : I = primewisePadicIdealOfExponents (primewisePadicIdealExponents I)
```

**Native source docstring:** Every closed ideal in the primewise p-adic ring is reconstructed from its
primewise exponents.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L138) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealExponents_idealOfExponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicIdealExponents_idealOfExponents (e : Nat.Primes → ℕ∞) : primewisePadicIdealExponents (primewisePadicIdealOfExponents e) = e
```

**Native source docstring:** The exponents of a product ideal are the exponents used to construct it.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L154) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealOfExponents_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicIdealOfExponents_injective : Function.Injective primewisePadicIdealOfExponents
```

**Native source docstring:** Primewise exponents uniquely determine their product ideal.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L165) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealOfExponents_inj

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicIdealOfExponents_inj {e f : Nat.Primes → ℕ∞} : primewisePadicIdealOfExponents e = primewisePadicIdealOfExponents f ↔ e = f
```

**Native source docstring:** Equality of ideals constructed from primewise exponents is exactly equality
of the exponent families.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L174) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealOfExponents_zero

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicIdealOfExponents_zero : primewisePadicIdealOfExponents 0 = ⊤
```

**Native source docstring:** Constant exponent zero gives the top ideal in the primewise product.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L183) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealOfExponents_top

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicIdealOfExponents_top : primewisePadicIdealOfExponents ⊤ = ⊥
```

**Native source docstring:** Constant infinite exponent gives the zero ideal in the primewise product.

[Source](../ProfiniteGroups/PrimewisePadicIdeals.lean#L190) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.PrimewisePadicKernel

9 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.instFactPrimeValNat_profiniteGroups_1

Kind: `theorem`.

```lean
theorem ProfiniteGrp.instFactPrimeValNat_profiniteGroups_1 (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../ProfiniteGroups/PrimewisePadicKernel.lean#L29) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRing

Kind: `def`.

```lean
abbrev ProfiniteGrp.primewisePadicRing : Type u
```

**Native source docstring:** The product ring underlying the primewise p-adic profinite group.

[Source](../ProfiniteGroups/PrimewisePadicKernel.lean#L31) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRingMultiplicativeEquiv

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicRingMultiplicativeEquiv : Multiplicative primewisePadicRing ≃ₜ* ↑primewisePadic.toProfinite.toTop
```

**Native source docstring:** The coordinatewise continuous multiplicative equivalence from the
primewise p-adic product ring, written multiplicatively, to
`primewisePadic`.

[Source](../ProfiniteGroups/PrimewisePadicKernel.lean#L35) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.denseRange_intCast_primewisePadicRing

Kind: `theorem`.

```lean
theorem ProfiniteGrp.denseRange_intCast_primewisePadicRing : DenseRange fun (n : ℤ) => ↑n
```

**Native source docstring:** Integer casts are dense in the product ring underlying
`primewisePadic`.

[Source](../ProfiniteGroups/PrimewisePadicKernel.lean#L47) (native source start line; generated entries may point to their parent).

#### AddSubgroup.toIdealOfIsClosedOfDenseIntCast

Kind: `def`.

```lean
def AddSubgroup.toIdealOfIsClosedOfDenseIntCast {R : Type u} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] (K : AddSubgroup R) (hK : IsClosed ↑K) (hℤ : DenseRange fun (n : ℤ) => ↑n) : Ideal R
```

**Native source docstring:** A closed additive subgroup of a topological ring with dense integer casts
is a left ideal.

For `k ∈ K`, the set of `r` such that `r * k ∈ K` is closed and contains
every integer cast.  Density therefore makes this set the whole ring.

[Source](../ProfiniteGroups/PrimewisePadicKernel.lean#L67) (native source start line; generated entries may point to their parent).

#### AddSubgroup.mem_toIdealOfIsClosedOfDenseIntCast

Kind: `theorem`.

```lean
theorem AddSubgroup.mem_toIdealOfIsClosedOfDenseIntCast {R : Type u} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] (K : AddSubgroup R) (hK : IsClosed ↑K) (hℤ : DenseRange fun (n : ℤ) => ↑n) (x : R) : x ∈ K.toIdealOfIsClosedOfDenseIntCast hK hℤ ↔ x ∈ K
```

**Native source docstring:** Membership in the ideal obtained from a closed additive subgroup is
unchanged.

[Source](../ProfiniteGroups/PrimewisePadicKernel.lean#L93) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdeal

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicKernelIdeal {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : Ideal primewisePadicRing
```

**Native source docstring:** The kernel of a continuous multiplicative homomorphism out of the
primewise p-adic group, regarded as an ideal of its underlying product ring.

[Source](../ProfiniteGroups/PrimewisePadicKernel.lean#L107) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.mem_primewisePadicKernelIdeal

Kind: `theorem`.

```lean
theorem ProfiniteGrp.mem_primewisePadicKernelIdeal {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (x : primewisePadicRing) : x ∈ primewisePadicKernelIdeal f ↔ f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) = 1
```

**Native source docstring:** Membership in the primewise p-adic kernel ideal is exactly vanishing
under the original multiplicative homomorphism.

[Source](../ProfiniteGroups/PrimewisePadicKernel.lean#L124) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isClosed_primewisePadicKernelIdeal

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isClosed_primewisePadicKernelIdeal {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : IsClosed ↑(primewisePadicKernelIdeal f)
```

**Native source docstring:** The carrier of the primewise p-adic kernel ideal is closed.

[Source](../ProfiniteGroups/PrimewisePadicKernel.lean#L135) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.PrimewisePadicKernelTransport

4 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.primewisePadicChangeUniverse_ringMultiplicativeEquiv

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicChangeUniverse_ringMultiplicativeEquiv (x : primewisePadicRing) : primewisePadicChangeUniverse (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) = primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd (primewisePadicRingChangeUniverse x))
```

**Native source docstring:** The continuous group universe change agrees with the algebraic ring
universe change under the multiplicative identifications.

[Source](../ProfiniteGroups/PrimewisePadicKernelTransport.lean#L26) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdeal_comp_changeUniverse

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdeal_comp_changeUniverse {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : primewisePadicKernelIdeal (f.comp ↑primewisePadicChangeUniverse) = Ideal.comap primewisePadicRingChangeUniverse (primewisePadicKernelIdeal f)
```

**Native source docstring:** Precomposition by universe change pulls back the actual kernel ideal,
without any surjectivity or generator hypothesis.

[Source](../ProfiniteGroups/PrimewisePadicKernelTransport.lean#L39) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelExponents_comp_changeUniverse

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelExponents_comp_changeUniverse {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : primewisePadicKernelExponents (f.comp ↑primewisePadicChangeUniverse) = primewisePadicKernelExponents f
```

**Native source docstring:** The coordinate exponents of the actual kernel are independent of the
universe used for the primewise p-adic source.

[Source](../ProfiniteGroups/PrimewisePadicKernelTransport.lean#L54) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelExponents_baseMapOfGenerator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelExponents_baseMapOfGenerator (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : primewisePadicKernelExponents (G.primewisePadicBaseMapOfGenerator g) = G.primewisePadicExponentsOfGenerator g
```

**Native source docstring:** The fixed-source map associated to any element, including a
non-generator, computes the same exponents as the original map.

[Source](../ProfiniteGroups/PrimewisePadicKernelTransport.lean#L67) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.PrimewisePadicQuotients

30 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.instFactPrimeValNat_profiniteGroups_3

Kind: `theorem`.

```lean
theorem ProfiniteGrp.instFactPrimeValNat_profiniteGroups_3 (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L30) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicToZModPow

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicToZModPow (p : Nat.Primes) (n : ℕ) : ULift.{u, 0} ℤ_[↑p] →+* ZMod (↑p ^ n)
```

**Native source docstring:** Reduction modulo `p ^ n` on an uplifted p-adic factor.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L32) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicToZModPow_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicToZModPow_apply (p : Nat.Primes) (n : ℕ) (x : ULift.{u, 0} ℤ_[↑p]) : (liftedPadicToZModPow p n) x = (PadicInt.toZModPow n) x.down
```

**Native source docstring:** Uplifted p-adic reduction acts by lowering the lift and reducing.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L37) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicToZModPow_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicToZModPow_surjective (p : Nat.Primes) (n : ℕ) : Function.Surjective ⇑(liftedPadicToZModPow p n)
```

**Native source docstring:** Uplifted reduction modulo `p ^ n` is surjective.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L44) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.ker_liftedPadicToZModPow

Kind: `theorem`.

```lean
theorem ProfiniteGrp.ker_liftedPadicToZModPow (p : Nat.Primes) (n : ℕ) : RingHom.ker (liftedPadicToZModPow p n) = liftedPadicIdealOfExponent p ↑n
```

**Native source docstring:** The kernel of uplifted reduction modulo `p ^ n` is the ideal with finite
exponent `n`.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L49) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientRingEquivZMod

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicQuotientRingEquivZMod (p : Nat.Primes) (n : ℕ) : ULift.{u, 0} ℤ_[↑p] ⧸ liftedPadicIdealOfExponent p ↑n ≃+* ZMod (↑p ^ n)
```

**Native source docstring:** A finite-exponent uplifted p-adic quotient is the expected residue ring.
This includes `n = 0`, where the target is `ZMod 1`.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L62) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientRingEquivZMod_mk

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicQuotientRingEquivZMod_mk (p : Nat.Primes) (n : ℕ) (x : ULift.{u, 0} ℤ_[↑p]) : (liftedPadicQuotientRingEquivZMod p n) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p ↑n)) x) = (PadicInt.toZModPow n) x.down
```

**Native source docstring:** The finite quotient equivalence is induced by p-adic reduction.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L72) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isOpen_liftedPadicIdealOfExponent_natCast

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isOpen_liftedPadicIdealOfExponent_natCast (p : Nat.Primes) (n : ℕ) : IsOpen ↑(liftedPadicIdealOfExponent p ↑n)
```

**Native source docstring:** A finite-exponent ideal in an uplifted p-adic factor is open.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L84) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.discreteTopology_liftedPadicQuotient_natCast

Kind: `theorem`.

```lean
theorem ProfiniteGrp.discreteTopology_liftedPadicQuotient_natCast (p : Nat.Primes) (n : ℕ) : DiscreteTopology (ULift.{u, 0} ℤ_[↑p] ⧸ liftedPadicIdealOfExponent p ↑n)
```

**Native source docstring:** The topology on a finite-exponent uplifted p-adic quotient is discrete.
The proof uses openness of the source ideal, rather than only discreteness of
the target residue ring.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L95) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientContinuousAddEquivZMod

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicQuotientContinuousAddEquivZMod (p : Nat.Primes) (n : ℕ) : ULift.{u, 0} ℤ_[↑p] ⧸ liftedPadicIdealOfExponent p ↑n ≃ₜ+ ZMod (↑p ^ n)
```

**Native source docstring:** The finite residue-ring equivalence as a continuous additive equivalence.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L105) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientContinuousAddEquivZMod_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicQuotientContinuousAddEquivZMod_apply (p : Nat.Primes) (n : ℕ) (x : ULift.{u, 0} ℤ_[↑p] ⧸ liftedPadicIdealOfExponent p ↑n) : (liftedPadicQuotientContinuousAddEquivZMod p n) x = (liftedPadicQuotientRingEquivZMod p n) x
```

**Native source docstring:** The continuous finite quotient equivalence is coherent with the ring
equivalence.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L115) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientContinuousAddEquivZero

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicQuotientContinuousAddEquivZero (p : Nat.Primes) : ULift.{u, 0} ℤ_[↑p] ⧸ liftedPadicIdealOfExponent p 0 ≃ₜ+ ZMod 1
```

**Native source docstring:** The zero-exponent factor is the quotient by the unit ideal and is
canonically continuously equivalent to `ZMod 1`.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L125) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientRingEquivTop

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicQuotientRingEquivTop (p : Nat.Primes) : ULift.{u, 0} ℤ_[↑p] ⧸ liftedPadicIdealOfExponent p ⊤ ≃+* ULift.{u, 0} ℤ_[↑p]
```

**Native source docstring:** The infinite-exponent quotient ring is the uplifted p-adic ring itself.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L135) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientRingEquivTop_mk

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicQuotientRingEquivTop_mk (p : Nat.Primes) (x : ULift.{u, 0} ℤ_[↑p]) : (liftedPadicQuotientRingEquivTop p) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p ⊤)) x) = x
```

**Native source docstring:** The infinite-exponent ring equivalence sends a quotient representative to
that representative.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L142) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientContinuousAddEquivTop

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicQuotientContinuousAddEquivTop (p : Nat.Primes) : ULift.{u, 0} ℤ_[↑p] ⧸ liftedPadicIdealOfExponent p ⊤ ≃ₜ+ ULift.{u, 0} ℤ_[↑p]
```

**Native source docstring:** The infinite-exponent quotient is continuously additively equivalent to
the uplifted p-adic factor.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L151) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientContinuousAddEquivTop_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicQuotientContinuousAddEquivTop_apply (p : Nat.Primes) (x : ULift.{u, 0} ℤ_[↑p] ⧸ liftedPadicIdealOfExponent p ⊤) : (liftedPadicQuotientContinuousAddEquivTop p) x = (liftedPadicQuotientRingEquivTop p) x
```

**Native source docstring:** The continuous infinite quotient equivalence is coherent with the ring
equivalence.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L168) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.padicQuotientFactorTop

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.padicQuotientFactorTop (p : Nat.Primes) : ProfiniteAddGrp.{u}
```

**Native source docstring:** The infinite p-adic branch, bundled as a profinite additive group in the
chosen universe.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L178) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.padicQuotientFactorNat

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.padicQuotientFactorNat (p : Nat.Primes) (n : ℕ) : ProfiniteAddGrp.{u}
```

**Native source docstring:** The finite residue branch, bundled as a profinite additive group in the
chosen universe.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L189) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.padicQuotientFactor

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.padicQuotientFactor (p : Nat.Primes) (e : ℕ∞) : ProfiniteAddGrp.{u}
```

**Native source docstring:** The universe-uniform factor model: an infinite exponent gives an uplifted
p-adic factor, and a finite exponent `n` gives an uplifted `ZMod (p ^ n)`.
The use of `ENat.recTopCoe` keeps the two cases explicit.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L201) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.padicQuotientFactor_top

Kind: `theorem`.

```lean
theorem ProfiniteGrp.padicQuotientFactor_top (p : Nat.Primes) : padicQuotientFactor p ⊤ = padicQuotientFactorTop p
```

**Native source docstring:** The infinite branch equation for the universe-uniform factor model.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L209) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.padicQuotientFactor_natCast

Kind: `theorem`.

```lean
theorem ProfiniteGrp.padicQuotientFactor_natCast (p : Nat.Primes) (n : ℕ) : padicQuotientFactor p ↑n = padicQuotientFactorNat p n
```

**Native source docstring:** The finite branch equation for the universe-uniform factor model.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L215) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.zmodContinuousAddEquivULift

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.zmodContinuousAddEquivULift (p : Nat.Primes) (n : ℕ) : ZMod (↑p ^ n) ≃ₜ+ ULift.{u, 0} (ZMod (↑p ^ n))
```

**Native source docstring:** The additive homeomorphism from a finite residue ring to its universe
lift.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L221) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientContinuousAddEquivFactor

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.liftedPadicQuotientContinuousAddEquivFactor (p : Nat.Primes) (e : ℕ∞) : ULift.{u, 0} ℤ_[↑p] ⧸ liftedPadicIdealOfExponent p e ≃ₜ+ ↑(padicQuotientFactor p e).toProfinite.toTop
```

**Native source docstring:** A quotient factor is continuously additively equivalent to its
universe-uniform finite-or-infinite model.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L228) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientContinuousAddEquivFactor_top_mk

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicQuotientContinuousAddEquivFactor_top_mk (p : Nat.Primes) (x : ULift.{u, 0} ℤ_[↑p]) : (liftedPadicQuotientContinuousAddEquivFactor p ⊤) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p ⊤)) x) = x
```

**Native source docstring:** In the infinite branch, the factor equivalence sends a quotient
representative to that representative.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L244) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.liftedPadicQuotientContinuousAddEquivFactor_natCast_mk

Kind: `theorem`.

```lean
theorem ProfiniteGrp.liftedPadicQuotientContinuousAddEquivFactor_natCast_mk (p : Nat.Primes) (n : ℕ) (x : ULift.{u, 0} ℤ_[↑p]) : (liftedPadicQuotientContinuousAddEquivFactor p ↑n) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p ↑n)) x) = { down := (PadicInt.toZModPow n) x.down }
```

**Native source docstring:** In a finite branch, the factor equivalence reduces modulo `p ^ n` and
then lifts the result to the chosen universe.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L255) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicQuotientModel

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicQuotientModel (e : Nat.Primes → ℕ∞) : ProfiniteAddGrp.{u}
```

**Native source docstring:** The product of the universe-uniform coordinate factor models.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L272) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.continuousAddEquivPiCongrRight

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.continuousAddEquivPiCongrRight {ι : Type u_1} {A : ι → Type u_2} {B : ι → Type u_3} [(i : ι) → Add (A i)] [(i : ι) → Add (B i)] [(i : ι) → TopologicalSpace (A i)] [(i : ι) → TopologicalSpace (B i)] (F : (i : ι) → A i ≃ₜ+ B i) : ((i : ι) → A i) ≃ₜ+ ((i : ι) → B i)
```

**Native source docstring:** The product of a dependent family of continuous additive equivalences.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L277) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.continuousAddEquivPiCongrRight_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.continuousAddEquivPiCongrRight_apply {ι : Type u_1} {A : ι → Type u_2} {B : ι → Type u_3} [(i : ι) → Add (A i)] [(i : ι) → Add (B i)] [(i : ι) → TopologicalSpace (A i)] [(i : ι) → TopologicalSpace (B i)] (F : (i : ι) → A i ≃ₜ+ B i) (x : (i : ι) → A i) (i : ι) : (continuousAddEquivPiCongrRight F) x i = (F i) (x i)
```

**Native source docstring:** The product equivalence acts coordinatewise.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L287) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicQuotientContinuousAddEquivModel

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicQuotientContinuousAddEquivModel (e : Nat.Primes → ℕ∞) : primewisePadicRing ⧸ primewisePadicIdealOfExponents e ≃ₜ+ ↑(primewisePadicQuotientModel e).toProfinite.toTop
```

**Native source docstring:** The quotient by an arbitrary primewise exponent ideal is continuously
additively equivalent, in the forward quotient-to-model direction, to the
complete product of its finite and infinite factor models.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L297) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicQuotientContinuousAddEquivModel_mk_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicQuotientContinuousAddEquivModel_mk_apply (e : Nat.Primes → ℕ∞) (x : primewisePadicRing) (p : Nat.Primes) : (primewisePadicQuotientContinuousAddEquivModel e) ((Ideal.Quotient.mk (primewisePadicIdealOfExponents e)) x) p = (liftedPadicQuotientContinuousAddEquivFactor p (e p)) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p (e p))) (x p))
```

**Native source docstring:** On a quotient representative, the mixed primewise model equivalence
reduces the selected coordinate and then applies its finite-or-infinite factor
equivalence.

[Source](../ProfiniteGroups/PrimewisePadicQuotients.lean#L309) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.PrimewisePadicSubgroups

34 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.instFactPrimeValNat_profiniteGroups_3

Kind: `theorem`.

```lean
theorem ProfiniteGrp.instFactPrimeValNat_profiniteGroups_3 (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L29) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicIdealOfExponents_le_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicIdealOfExponents_le_iff {e d : Nat.Primes → ℕ∞} : primewisePadicIdealOfExponents e ≤ primewisePadicIdealOfExponents d ↔ ∀ (p : Nat.Primes), d p ≤ e p
```

**Native source docstring:** Inclusion of primewise p-adic product ideals is reverse pointwise
comparison of their exponent families.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L31) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupIdeal

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedAddSubgroupIdeal (K : ClosedAddSubgroup primewisePadicRing) : Ideal primewisePadicRing
```

**Native source docstring:** The ideal carried by a closed additive subgroup of the primewise p-adic
ring.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L54) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupExponents

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedAddSubgroupExponents (K : ClosedAddSubgroup primewisePadicRing) : Nat.Primes → ℕ∞
```

**Native source docstring:** The coordinatewise exponents of a closed additive subgroup of the
primewise p-adic ring.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L62) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents (e : Nat.Primes → ℕ∞) : ClosedAddSubgroup primewisePadicRing
```

**Native source docstring:** The closed additive subgroup having the prescribed primewise exponents.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L68) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.mem_primewisePadicClosedAddSubgroupOfExponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.mem_primewisePadicClosedAddSubgroupOfExponents (e : Nat.Primes → ℕ∞) (x : primewisePadicRing) : x ∈ primewisePadicClosedAddSubgroupOfExponents e ↔ ∀ (p : Nat.Primes), x p ∈ liftedPadicIdealOfExponent p (e p)
```

**Native source docstring:** Membership in the closed additive subgroup with prescribed exponents is
coordinatewise membership in the corresponding p-adic ideals.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L74) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_exponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_exponents (K : ClosedAddSubgroup primewisePadicRing) : primewisePadicClosedAddSubgroupOfExponents (primewisePadicClosedAddSubgroupExponents K) = K
```

**Native source docstring:** A closed additive subgroup is reconstructed from its primewise
exponents.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L83) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupExponents_ofExponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedAddSubgroupExponents_ofExponents (e : Nat.Primes → ℕ∞) : primewisePadicClosedAddSubgroupExponents (primewisePadicClosedAddSubgroupOfExponents e) = e
```

**Native source docstring:** Extracting exponents from the closed additive subgroup constructed from
them recovers the original family.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L102) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_injective : Function.Injective primewisePadicClosedAddSubgroupOfExponents
```

**Native source docstring:** Primewise exponents uniquely determine a closed additive subgroup.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L118) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_inj

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_inj {e d : Nat.Primes → ℕ∞} : primewisePadicClosedAddSubgroupOfExponents e = primewisePadicClosedAddSubgroupOfExponents d ↔ e = d
```

**Native source docstring:** Equality of closed additive subgroups constructed from exponents is
exactly equality of their exponent families.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L126) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_le_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_le_iff {e d : Nat.Primes → ℕ∞} : primewisePadicClosedAddSubgroupOfExponents e ≤ primewisePadicClosedAddSubgroupOfExponents d ↔ ∀ (p : Nat.Primes), d p ≤ e p
```

**Native source docstring:** The inclusion order on closed additive subgroups is the reverse
pointwise order on exponent families.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L135) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupOrderIso

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedAddSubgroupOrderIso : ClosedAddSubgroup primewisePadicRing ≃o (Nat.Primes → ℕ∞)ᵒᵈ
```

**Native source docstring:** Closed additive subgroups of the primewise p-adic ring, ordered by
inclusion, correspond to exponent families with the pointwise order
reversed.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L145) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_zero_toAddSubgroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_zero_toAddSubgroup : ↑(primewisePadicClosedAddSubgroupOfExponents 0) = ⊤
```

**Native source docstring:** Exponent zero gives the whole underlying additive subgroup.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L171) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_top_toAddSubgroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedAddSubgroupOfExponents_top_toAddSubgroup : ↑(primewisePadicClosedAddSubgroupOfExponents ⊤) = ⊥
```

**Native source docstring:** Infinite exponent at every prime gives the trivial underlying additive
subgroup.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L179) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupToClosedSubgroup

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedAddSubgroupToClosedSubgroup (K : ClosedAddSubgroup primewisePadicRing) : ClosedSubgroup ↑primewisePadic.toProfinite.toTop
```

**Native source docstring:** Transport a closed additive subgroup of the underlying ring to a closed
multiplicative subgroup of `primewisePadic`.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L188) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupToClosedAddSubgroup

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedSubgroupToClosedAddSubgroup (H : ClosedSubgroup ↑primewisePadic.toProfinite.toTop) : ClosedAddSubgroup primewisePadicRing
```

**Native source docstring:** Pull a closed subgroup of `primewisePadic` back to a closed additive
subgroup of its underlying product ring.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L201) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupToClosedAddSubgroup_toClosedSubgroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedSubgroupToClosedAddSubgroup_toClosedSubgroup (K : ClosedAddSubgroup primewisePadicRing) : primewisePadicClosedSubgroupToClosedAddSubgroup (primewisePadicClosedAddSubgroupToClosedSubgroup K) = K
```

**Native source docstring:** Transporting a closed additive subgroup to `primewisePadic` and back is
the identity.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L216) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupToClosedSubgroup_toClosedAddSubgroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedAddSubgroupToClosedSubgroup_toClosedAddSubgroup (H : ClosedSubgroup ↑primewisePadic.toProfinite.toTop) : primewisePadicClosedAddSubgroupToClosedSubgroup (primewisePadicClosedSubgroupToClosedAddSubgroup H) = H
```

**Native source docstring:** Pulling back a closed subgroup of `primewisePadic` and transporting it
forward is the identity.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L233) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedAddSubgroupClosedSubgroupOrderIso

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedAddSubgroupClosedSubgroupOrderIso : ClosedAddSubgroup primewisePadicRing ≃o ClosedSubgroup ↑primewisePadic.toProfinite.toTop
```

**Native source docstring:** The continuous multiplicative equivalence identifies closed additive
subgroups of the underlying ring with closed subgroups of
`primewisePadic`, preserving inclusion.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L247) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupOfExponents

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedSubgroupOfExponents (e : Nat.Primes → ℕ∞) : ClosedSubgroup ↑primewisePadic.toProfinite.toTop
```

**Native source docstring:** The closed subgroup of `primewisePadic` having the prescribed additive
coordinate exponents.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L268) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupExponents

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedSubgroupExponents (H : ClosedSubgroup ↑primewisePadic.toProfinite.toTop) : Nat.Primes → ℕ∞
```

**Native source docstring:** The additive coordinate exponents of a closed subgroup of
`primewisePadic`.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L275) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.mem_primewisePadicClosedSubgroupOfExponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.mem_primewisePadicClosedSubgroupOfExponents (e : Nat.Primes → ℕ∞) (x : ↑primewisePadic.toProfinite.toTop) : x ∈ primewisePadicClosedSubgroupOfExponents e ↔ ∀ (p : Nat.Primes), Multiplicative.toAdd (primewisePadicRingMultiplicativeEquiv.symm x) p ∈ liftedPadicIdealOfExponent p (e p)
```

**Native source docstring:** Membership in a closed subgroup with prescribed exponents is tested on
the additive coordinates obtained from the inverse continuous equivalence.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L282) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_exponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_exponents (H : ClosedSubgroup ↑primewisePadic.toProfinite.toTop) : primewisePadicClosedSubgroupOfExponents (primewisePadicClosedSubgroupExponents H) = H
```

**Native source docstring:** A closed subgroup of `primewisePadic` is reconstructed from its
coordinate exponents.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L306) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupExponents_ofExponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedSubgroupExponents_ofExponents (e : Nat.Primes → ℕ∞) : primewisePadicClosedSubgroupExponents (primewisePadicClosedSubgroupOfExponents e) = e
```

**Native source docstring:** Extracting exponents from a closed subgroup constructed from them
recovers the original family.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L318) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupOrderIso

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicClosedSubgroupOrderIso : ClosedSubgroup ↑primewisePadic.toProfinite.toTop ≃o (Nat.Primes → ℕ∞)ᵒᵈ
```

**Native source docstring:** Closed subgroups of `primewisePadic`, ordered by inclusion, correspond
to additive coordinate exponent families with the pointwise order reversed.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L330) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_le_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_le_iff {e d : Nat.Primes → ℕ∞} : primewisePadicClosedSubgroupOfExponents e ≤ primewisePadicClosedSubgroupOfExponents d ↔ ∀ (p : Nat.Primes), d p ≤ e p
```

**Native source docstring:** The inclusion order on closed multiplicative subgroups is the reverse
pointwise order on exponent families.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L337) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_inj

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_inj {e d : Nat.Primes → ℕ∞} : primewisePadicClosedSubgroupOfExponents e = primewisePadicClosedSubgroupOfExponents d ↔ e = d
```

**Native source docstring:** Primewise exponents uniquely determine a closed subgroup of
`primewisePadic`.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L356) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_zero_toSubgroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_zero_toSubgroup : ↑(primewisePadicClosedSubgroupOfExponents 0) = ⊤
```

**Native source docstring:** Exponent zero gives the whole underlying multiplicative subgroup.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L368) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_top_toSubgroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicClosedSubgroupOfExponents_top_toSubgroup : ↑(primewisePadicClosedSubgroupOfExponents ⊤) = ⊥
```

**Native source docstring:** Infinite exponent at every prime gives the trivial underlying
multiplicative subgroup.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L377) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelExponents

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicKernelExponents {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : Nat.Primes → ℕ∞
```

**Native source docstring:** The primewise exponents of the kernel of a continuous multiplicative
homomorphism.  The target needs only a group, a topology, and the T1 axiom
used to make the kernel closed.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L394) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdeal_eq_idealOfExponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdeal_eq_idealOfExponents {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : primewisePadicKernelIdeal f = primewisePadicIdealOfExponents (primewisePadicKernelExponents f)
```

**Native source docstring:** The closed kernel ideal is reconstructed from its primewise exponents.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L402) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadic_map_eq_one_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadic_map_eq_one_iff {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (x : ↑primewisePadic.toProfinite.toTop) : f x = 1 ↔ ∀ (p : Nat.Primes), Multiplicative.toAdd (primewisePadicRingMultiplicativeEquiv.symm x) p ∈ liftedPadicIdealOfExponent p (primewisePadicKernelExponents f p)
```

**Native source docstring:** An element is killed by a continuous homomorphism exactly when each of
its additive coordinates belongs to the p-adic ideal specified by the kernel
exponent.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L410) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadic_injective_iff_kernelExponents_eq_top

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadic_injective_iff_kernelExponents_eq_top {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : Function.Injective ⇑f ↔ ∀ (p : Nat.Primes), primewisePadicKernelExponents f p = ⊤
```

**Native source docstring:** A continuous homomorphism from `primewisePadic` is injective exactly when
every kernel exponent is infinite.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L479) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadic_eq_one_iff_kernelExponents_eq_zero

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadic_eq_one_iff_kernelExponents_eq_zero {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : f = 1 ↔ ∀ (p : Nat.Primes), primewisePadicKernelExponents f p = 0
```

**Native source docstring:** A continuous homomorphism from `primewisePadic` is trivial exactly when
every kernel exponent is zero.

[Source](../ProfiniteGroups/PrimewisePadicSubgroups.lean#L500) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.ProP

69 native named entries; 6 native instance-table rows.

#### IsPGroup.prod

Kind: `theorem`.

```lean
theorem IsPGroup.prod {p : ℕ} {G : Type u_1} {H : Type u_2} [Group G] [Group H] (hG : IsPGroup p G) (hH : IsPGroup p H) : IsPGroup p (G × H)
```

**Native source docstring:** A product of two `p`-groups is a `p`-group.

[Source](../ProfiniteGroups/ProP.lean#L45) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProP

Kind: `class`.

```lean
class ProfiniteGrp.IsProP (p : ℕ) (G : ProfiniteGrp.{u}) [Fact (Nat.Prime p)] : Prop
```

**Native source docstring:** A profinite group is pro-`p` when every quotient by an open normal
subgroup is a finite `p`-group.

[Source](../ProfiniteGroups/ProP.lean#L62) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProP.mk

Kind: `ctor`.

```lean
constructor ProfiniteGrp.IsProP.mk : ∀ {p : ℕ} {G : ProfiniteGrp.{u}} [inst : Fact (Nat.Prime p)], (∀ (U : OpenNormalSubgroup ↑G.toProfinite.toTop), IsPGroup p (↑G.toProfinite.toTop ⧸ ↑U.toOpenSubgroup)) → ProfiniteGrp.IsProP p G
```

**Original catalogue explanation (not a Lean docstring):** Constructor taking a proof that every open-normal finite quotient is a finite p-group.

[Source](../ProfiniteGroups/ProP.lean#L62) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProP.quotient_isPGroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProP.quotient_isPGroup {p : ℕ} {G : ProfiniteGrp.{u}} {inst✝ : Fact (Nat.Prime p)} [self : IsProP p G] (U : OpenNormalSubgroup ↑G.toProfinite.toTop) : IsPGroup p (↑G.toProfinite.toTop ⧸ ↑U.toOpenSubgroup)
```

**Original catalogue explanation (not a Lean docstring):** Projection of the pro-p property to an individual open-normal quotient.

[Source](../ProfiniteGroups/ProP.lean#L65) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProP.quotient

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProP.quotient {p : ℕ} [Fact (Nat.Prime p)] {G : ProfiniteGrp.{u}} (hG : IsProP p G) (U : OpenNormalSubgroup ↑G.toProfinite.toTop) : IsPGroup p (↑G.toProfinite.toTop ⧸ ↑U.toOpenSubgroup)
```

**Native source docstring:** Extract the defining `p`-group property of a quotient by an open normal
subgroup from a supplied proof that the profinite group is pro-`p`.

[Source](../ProfiniteGroups/ProP.lean#L72) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProP.of_isPGroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProP.of_isPGroup {p : ℕ} [Fact (Nat.Prime p)] {G : ProfiniteGrp.{u}} (hG : IsPGroup p ↑G.toProfinite.toTop) : IsProP p G
```

**Native source docstring:** An algebraic `p`-group with a profinite topology is pro-`p`.

[Source](../ProfiniteGroups/ProP.lean#L78) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProP.of_continuousMulEquiv

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProP.of_continuousMulEquiv {p : ℕ} [Fact (Nat.Prime p)] {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : IsProP p G) (e : ↑G.toProfinite.toTop ≃ₜ* ↑H.toProfinite.toTop) : IsProP p H
```

**Native source docstring:** The pro-`p` property is preserved by a continuous group equivalence.

[Source](../ProfiniteGroups/ProP.lean#L82) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient

Kind: `structure`.

```lean
structure ProfiniteGrp.MaximalProPQuotient.Quotient (p : ℕ) (G : ProfiniteGrp.{u}) extends OpenNormalSubgroup ↑G.toProfinite.toTop : Type u
```

**Native source docstring:** An open normal subgroup whose quotient is a `p`-group.

[Source](../ProfiniteGroups/ProP.lean#L104) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.mk

Kind: `ctor`.

```lean
constructor ProfiniteGrp.MaximalProPQuotient.Quotient.mk : {p : ℕ} → {G : ProfiniteGrp.{u}} → (toOpenNormalSubgroup : OpenNormalSubgroup ↑G.toProfinite.toTop) → IsPGroup p (↑G.toProfinite.toTop ⧸ ↑toOpenNormalSubgroup.toOpenSubgroup) → ProfiniteGrp.MaximalProPQuotient.Quotient p G
```

**Original catalogue explanation (not a Lean docstring):** Constructor for an open normal subgroup together with its p-group quotient condition.

[Source](../ProfiniteGroups/ProP.lean#L104) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.ext

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.Quotient.ext {p : ℕ} {G : ProfiniteGrp.{u}} {x y : Quotient p G} (carrier : (↑x.toOpenSubgroup).carrier = (↑y.toOpenSubgroup).carrier) : x = y
```

**Original catalogue explanation (not a Lean docstring):** Extensionality for eligible p-quotients uses their inherited subgroup data.

[Source](../ProfiniteGroups/ProP.lean#L105) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.ext_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.Quotient.ext_iff {p : ℕ} {G : ProfiniteGrp.{u}} {x y : Quotient p G} : x = y ↔ (↑x.toOpenSubgroup).carrier = (↑y.toOpenSubgroup).carrier
```

**Original catalogue explanation (not a Lean docstring):** Equality of eligible p-quotients is characterized by equality of their open normal subgroups.

[Source](../ProfiniteGroups/ProP.lean#L105) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.toOpenNormalSubgroup

Kind: `def`.

```lean
abbrev ProfiniteGrp.MaximalProPQuotient.Quotient.toOpenNormalSubgroup {p : ℕ} {G : ProfiniteGrp.{u}} (self : Quotient p G) : OpenNormalSubgroup ↑G.toProfinite.toTop
```

**Original catalogue explanation (not a Lean docstring):** Projection from an eligible p-quotient to its open normal subgroup.

[Source](../ProfiniteGroups/ProP.lean#L106) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.isPGroup'

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.Quotient.isPGroup' {p : ℕ} {G : ProfiniteGrp.{u}} (self : Quotient p G) : IsPGroup p (↑G.toProfinite.toTop ⧸ ↑self.toOpenSubgroup)
```

**Original catalogue explanation (not a Lean docstring):** An eligible quotient carries the finite p-group property specified in its structure.

[Source](../ProfiniteGroups/ProP.lean#L107) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.toOpenNormalSubgroup_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.Quotient.toOpenNormalSubgroup_injective (p : ℕ) (G : ProfiniteGrp.{u}) : Function.Injective toOpenNormalSubgroup
```

**Native source docstring:** A finite `p`-group quotient kernel is determined by its underlying open
normal subgroup; its `p`-group certificate is proof-irrelevant.

[Source](../ProfiniteGroups/ProP.lean#L112) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.instPartialOrder

Kind: `instance`.

```lean
instance ProfiniteGrp.MaximalProPQuotient.Quotient.instPartialOrder (p : ℕ) (G : ProfiniteGrp.{u}) : PartialOrder (Quotient p G)
```

**Original catalogue explanation (not a Lean docstring):** Orders the eligible p-quotients through their open normal subgroup order.

[Source](../ProfiniteGroups/ProP.lean#L120) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.quotient_inf_isPGroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.Quotient.quotient_inf_isPGroup (p : ℕ) (G : ProfiniteGrp.{u}) (U V : Quotient p G) : IsPGroup p (↑G.toProfinite.toTop ⧸ ↑(U.toOpenNormalSubgroup ⊓ V.toOpenNormalSubgroup).toOpenSubgroup)
```

**Native source docstring:** Intersecting two defining kernels still gives a `p`-group quotient: it
embeds in the product of the two original quotients. This supplies `Quotient.inf`.

[Source](../ProfiniteGroups/ProP.lean#L125) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.inf

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.Quotient.inf (p : ℕ) (G : ProfiniteGrp.{u}) (U V : Quotient p G) : Quotient p G
```

**Native source docstring:** Intersections of pro-`p` quotient kernels are again pro-`p` quotient
kernels.

[Source](../ProfiniteGroups/ProP.lean#L148) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.instSemilatticeInf

Kind: `instance`.

```lean
instance ProfiniteGrp.MaximalProPQuotient.Quotient.instSemilatticeInf (p : ℕ) (G : ProfiniteGrp.{u}) : SemilatticeInf (Quotient p G)
```

**Original catalogue explanation (not a Lean docstring):** Common refinement by intersection equips eligible p-quotients with infima.

[Source](../ProfiniteGroups/ProP.lean#L154) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.topOpenNormal

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.Quotient.topOpenNormal (G : ProfiniteGrp.{u}) : OpenNormalSubgroup ↑G.toProfinite.toTop
```

**Native source docstring:** The whole group as an open normal subgroup.

[Source](../ProfiniteGroups/ProP.lean#L165) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.top

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.Quotient.top (p : ℕ) (G : ProfiniteGrp.{u}) : Quotient p G
```

**Native source docstring:** The trivial quotient is a `p`-group quotient.

[Source](../ProfiniteGroups/ProP.lean#L170) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.instNonempty

Kind: `instance`.

```lean
instance ProfiniteGrp.MaximalProPQuotient.Quotient.instNonempty (p : ℕ) (G : ProfiniteGrp.{u}) : Nonempty (Quotient p G)
```

**Original catalogue explanation (not a Lean docstring):** The trivial quotient gives a nonempty eligible p-quotient category.

[Source](../ProfiniteGroups/ProP.lean#L179) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.Quotient.instOrderTop

Kind: `instance`.

```lean
instance ProfiniteGrp.MaximalProPQuotient.Quotient.instOrderTop (p : ℕ) (G : ProfiniteGrp.{u}) : OrderTop (Quotient p G)
```

**Original catalogue explanation (not a Lean docstring):** The indiscrete open normal subgroup is the top eligible p-quotient.

[Source](../ProfiniteGroups/ProP.lean#L181) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.finiteGrpDiagram

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.finiteGrpDiagram (p : ℕ) (G : ProfiniteGrp.{u}) : CategoryTheory.Functor (Quotient p G) FiniteGrp.{u}
```

**Native source docstring:** The diagram of finite `p`-group quotients of a profinite group.

[Source](../ProfiniteGroups/ProP.lean#L191) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.diagram

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.diagram (p : ℕ) (G : ProfiniteGrp.{u}) : CategoryTheory.Functor (Quotient p G) ProfiniteGrp.{u}
```

**Native source docstring:** The finite `p`-group quotient diagram viewed in profinite groups.

[Source](../ProfiniteGroups/ProP.lean#L199) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.product

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.product (p : ℕ) (G : ProfiniteGrp.{u}) : ProfiniteGrp.{u}
```

**Native source docstring:** The maximal pro-`p` quotient, constructed as the limit of all finite
`p`-group quotients.

[Source](../ProfiniteGroups/ProP.lean#L203) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.etaFn

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.etaFn (p : ℕ) (G : ProfiniteGrp.{u}) (x : ↑G.toProfinite.toTop) : ↑(product p G).toProfinite.toTop
```

**Native source docstring:** The canonical map to the maximal pro-`p` quotient, as a function.

[Source](../ProfiniteGroups/ProP.lean#L207) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.eta

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.eta (p : ℕ) (G : ProfiniteGrp.{u}) : G ⟶ product p G
```

**Native source docstring:** The canonical quotient morphism to the maximal pro-`p` quotient.

[Source](../ProfiniteGroups/ProP.lean#L211) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.denseRange

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.denseRange (p : ℕ) (G : ProfiniteGrp.{u}) : DenseRange (etaFn p G)
```

**Native source docstring:** The canonical map to the maximal pro-`p` quotient has dense range.

[Source](../ProfiniteGroups/ProP.lean#L237) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.eta_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.eta_surjective (p : ℕ) (G : ProfiniteGrp.{u}) : Function.Surjective ⇑(Hom.hom (eta p G))
```

**Native source docstring:** The canonical map onto the maximal pro-`p` quotient is surjective.

[Source](../ProfiniteGroups/ProP.lean#L258) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.exists_quotient_le_comap

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.exists_quotient_le_comap (p : ℕ) (G : ProfiniteGrp.{u}) (H : OpenNormalSubgroup ↑(product p G).toProfinite.toTop) : ∃ (U : Quotient p G), ↑U.toOpenSubgroup ≤ Subgroup.comap (Hom.hom (eta p G)).toMonoidHom ↑H.toOpenSubgroup
```

**Native source docstring:** Every open normal subgroup of the maximal pro-`p` quotient pulls back
to contain one of the finite `p`-group quotient kernels.

[Source](../ProfiniteGroups/ProP.lean#L267) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.openQuotientMap

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.openQuotientMap (p : ℕ) (G : ProfiniteGrp.{u}) (H : OpenNormalSubgroup ↑(product p G).toProfinite.toTop) (U : Quotient p G) (hU : ↑U.toOpenSubgroup ≤ Subgroup.comap (Hom.hom (eta p G)).toMonoidHom ↑H.toOpenSubgroup) : ↑G.toProfinite.toTop ⧸ ↑U.toOpenSubgroup →* ↑(product p G).toProfinite.toTop ⧸ ↑H.toOpenSubgroup
```

**Native source docstring:** The finite quotient induced by an open normal subgroup of the maximal
pro-`p` quotient and a smaller defining `p`-group quotient kernel.

[Source](../ProfiniteGroups/ProP.lean#L299) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.quotientMap_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.quotientMap_surjective (p : ℕ) (G : ProfiniteGrp.{u}) (H : OpenNormalSubgroup ↑(product p G).toProfinite.toTop) (U : Quotient p G) (hU : ↑U.toOpenSubgroup ≤ Subgroup.comap (Hom.hom (eta p G)).toMonoidHom ↑H.toOpenSubgroup) : Function.Surjective ⇑(openQuotientMap p G H U hU)
```

**Native source docstring:** A finite quotient of the maximal pro-`p` quotient is reached from a
refining finite pro-`p` quotient of the original group.

[Source](../ProfiniteGroups/ProP.lean#L310) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.product_isProP

Kind: `instance`.

```lean
instance ProfiniteGrp.MaximalProPQuotient.product_isProP (p : ℕ) [Fact (Nat.Prime p)] (G : ProfiniteGrp.{u}) : IsProP p (product p G)
```

**Native source docstring:** The maximal pro-`p` quotient is a pro-`p` group.

[Source](../ProfiniteGroups/ProP.lean#L322) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.preimage

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.preimage (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] (f : ↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (H : OpenNormalSubgroup ↑P.toProfinite.toTop) : Quotient p G
```

**Native source docstring:** Pulling an open normal subgroup of a pro-`p` target back along a
continuous homomorphism gives a finite `p`-group quotient kernel.

[Source](../ProfiniteGroups/ProP.lean#L332) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.preimage_le

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.preimage_le (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] {f : ↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop} {H K : OpenNormalSubgroup ↑P.toProfinite.toTop} (h : H ≤ K) : preimage p f H ≤ preimage p f K
```

**Native source docstring:** Refining a target quotient kernel refines its pullback kernel. This makes
the finite quotient maps compatible in the construction of `lift`.

[Source](../ProfiniteGroups/ProP.lean#L353) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.quotientMap

Kind: `def`.

```lean
def ProfiniteGrp.MaximalProPQuotient.quotientMap (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] (f : ↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (H : OpenNormalSubgroup ↑P.toProfinite.toTop) : ↧(↑G.toProfinite.toTop ⧸ ↑(preimage p f H).toOpenSubgroup) ⟶ ↧(↑P.toProfinite.toTop ⧸ ↑H.toOpenSubgroup)
```

**Native source docstring:** The finite quotient map induced by a homomorphism to a pro-`p` target.

[Source](../ProfiniteGroups/ProP.lean#L359) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.lift

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.MaximalProPQuotient.lift (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] (f : ↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) : product p G ⟶ P
```

**Native source docstring:** Every continuous homomorphism from a profinite group to a pro-`p`
group factors through its maximal pro-`p` quotient.

[Source](../ProfiniteGroups/ProP.lean#L366) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.lift_eta

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.lift_eta (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] (f : ↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) : CategoryTheory.CategoryStruct.comp (eta p G) (lift p f) = ofHom f
```

**Native source docstring:** Precomposing the universal lift with the canonical quotient map recovers
the supplied continuous homomorphism, viewed as a profinite-group morphism.

[Source](../ProfiniteGroups/ProP.lean#L388) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.lift_eta_assoc

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.lift_eta_assoc (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] (f : ↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) {Z : ProfiniteGrp.{u}} (h : P ⟶ Z) : CategoryTheory.CategoryStruct.comp (eta p G) (CategoryTheory.CategoryStruct.comp (lift p f) h) = CategoryTheory.CategoryStruct.comp (ofHom f) h
```

**Native source docstring:** Precomposing the universal lift with the canonical quotient map recovers
the supplied continuous homomorphism, viewed as a profinite-group morphism.

[Source](../ProfiniteGroups/ProP.lean#L390) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.lift_unique

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.lift_unique (p : ℕ) {G P : ProfiniteGrp.{u}} (f g : product p G ⟶ P) (h : CategoryTheory.CategoryStruct.comp (eta p G) f = CategoryTheory.CategoryStruct.comp (eta p G) g) : f = g
```

**Native source docstring:** Morphisms out of the maximal pro-`p` quotient are determined by their
composites with the canonical quotient map.

[Source](../ProfiniteGroups/ProP.lean#L401) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.lift_comp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.lift_comp (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] {Q : ProfiniteGrp.{u}} [IsProP p Q] (f : ↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (g : P ⟶ Q) : CategoryTheory.CategoryStruct.comp (lift p f) g = lift p ((Hom.hom g).comp f)
```

**Native source docstring:** The universal lift is natural in the pro-`p` target.

[Source](../ProfiniteGroups/ProP.lean#L411) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.lift_comp_assoc

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.lift_comp_assoc (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] {Q : ProfiniteGrp.{u}} [IsProP p Q] (f : ↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (g : P ⟶ Q) {Z : ProfiniteGrp.{u}} (h : Q ⟶ Z) : CategoryTheory.CategoryStruct.comp (lift p f) (CategoryTheory.CategoryStruct.comp g h) = CategoryTheory.CategoryStruct.comp (lift p ((Hom.hom g).comp f)) h
```

**Native source docstring:** The universal lift is natural in the pro-`p` target.

[Source](../ProfiniteGroups/ProP.lean#L412) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.homEquiv

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.MaximalProPQuotient.homEquiv (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] : (product p G ⟶ P) ≃ (↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop)
```

**Native source docstring:** Continuous homomorphisms from a profinite group to a pro-`p` group are
equivalent to morphisms from its maximal pro-`p` quotient.

[Source](../ProfiniteGroups/ProP.lean#L418) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.homEquiv_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.homEquiv_apply (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] (f : product p G ⟶ P) : (homEquiv p) f = (Hom.hom f).comp (Hom.hom (eta p G))
```

**Native source docstring:** The forward universal-property correspondence precomposes a morphism
with the canonical quotient map and returns a continuous homomorphism.

[Source](../ProfiniteGroups/ProP.lean#L433) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.homEquiv_symm_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.homEquiv_symm_apply (p : ℕ) [Fact (Nat.Prime p)] {G P : ProfiniteGrp.{u}} [IsProP p P] (f : ↑G.toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) : (homEquiv p).symm f = lift p f
```

**Native source docstring:** The inverse universal-property correspondence is the factorization
`lift p` through the maximal pro-`p` quotient.

[Source](../ProfiniteGroups/ProP.lean#L439) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.isoOfIsProP

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.MaximalProPQuotient.isoOfIsProP (p : ℕ) [Fact (Nat.Prime p)] (G : ProfiniteGrp.{u}) [IsProP p G] : product p G ≅ G
```

**Native source docstring:** The maximal pro-`p` quotient of a pro-`p` group is canonically isomorphic
to the group itself.

[Source](../ProfiniteGroups/ProP.lean#L447) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.map

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.MaximalProPQuotient.map (p : ℕ) [Fact (Nat.Prime p)] {G H : ProfiniteGrp.{u}} (f : G ⟶ H) : product p G ⟶ product p H
```

**Native source docstring:** A morphism of profinite groups induces a morphism of their maximal
pro-`p` quotients.

[Source](../ProfiniteGroups/ProP.lean#L459) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.eta_map

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.eta_map (p : ℕ) [Fact (Nat.Prime p)] {G H : ProfiniteGrp.{u}} (f : G ⟶ H) : CategoryTheory.CategoryStruct.comp (eta p G) (map p f) = CategoryTheory.CategoryStruct.comp f (eta p H)
```

**Native source docstring:** The canonical quotient maps commute with the morphism induced by `f`.
This is the naturality equation for the maximal pro-`p` quotient.

[Source](../ProfiniteGroups/ProP.lean#L465) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.eta_map_assoc

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.eta_map_assoc (p : ℕ) [Fact (Nat.Prime p)] {G H : ProfiniteGrp.{u}} (f : G ⟶ H) {Z : ProfiniteGrp.{u}} (h : product p H ⟶ Z) : CategoryTheory.CategoryStruct.comp (eta p G) (CategoryTheory.CategoryStruct.comp (map p f) h) = CategoryTheory.CategoryStruct.comp f (CategoryTheory.CategoryStruct.comp (eta p H) h)
```

**Native source docstring:** The canonical quotient maps commute with the morphism induced by `f`.
This is the naturality equation for the maximal pro-`p` quotient.

[Source](../ProfiniteGroups/ProP.lean#L467) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.map_id

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.map_id (p : ℕ) [Fact (Nat.Prime p)] (G : ProfiniteGrp.{u}) : map p (CategoryTheory.CategoryStruct.id G) = CategoryTheory.CategoryStruct.id (product p G)
```

**Native source docstring:** The identity morphism induces the identity on the maximal pro-`p`
quotient; this is the identity law used by `functor`.

[Source](../ProfiniteGroups/ProP.lean#L474) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.map_comp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.MaximalProPQuotient.map_comp (p : ℕ) [Fact (Nat.Prime p)] {G H K : ProfiniteGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) : CategoryTheory.CategoryStruct.comp (map p f) (map p g) = map p (CategoryTheory.CategoryStruct.comp f g)
```

**Native source docstring:** The induced quotient morphisms respect composition, with `f` applied
before `g`; this is the composition law used by `functor`.

[Source](../ProfiniteGroups/ProP.lean#L482) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.MaximalProPQuotient.functor

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.MaximalProPQuotient.functor (p : ℕ) [Fact (Nat.Prime p)] : CategoryTheory.Functor ProfiniteGrp.{u} ProfiniteGrp.{u}
```

**Native source docstring:** Taking the maximal pro-`p` quotient is functorial.

[Source](../ProfiniteGroups/ProP.lean#L490) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.product

Kind: `def`.

```lean
abbrev ProfiniteGrp.FreeProPProduct.product {ι : Type v} (p : ℕ) (G : ι → ProfiniteGrp.{u}) : ProfiniteGrp.{max u v}
```

**Native source docstring:** The free pro-`p` product of a family of profinite groups is the maximal
pro-`p` quotient of their free profinite product.

[Source](../ProfiniteGroups/ProP.lean#L505) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.product_isProP

Kind: `instance`.

```lean
instance ProfiniteGrp.FreeProPProduct.product_isProP {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] (G : ι → ProfiniteGrp.{u}) : IsProP p (product p G)
```

**Native source docstring:** The free pro-`p` product is pro-`p` even when no pro-`p` assumption is
made on the factors, since it is constructed as a maximal pro-`p` quotient.

[Source](../ProfiniteGroups/ProP.lean#L510) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.of

Kind: `def`.

```lean
def ProfiniteGrp.FreeProPProduct.of {ι : Type v} (p : ℕ) (G : ι → ProfiniteGrp.{u}) (i : ι) : ↑(G i).toProfinite.toTop →ₜ* ↑(product p G).toProfinite.toTop
```

**Native source docstring:** The canonical continuous homomorphism from a factor to the free pro-`p`
product.

[Source](../ProfiniteGroups/ProP.lean#L514) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.lift

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FreeProPProduct.lift {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} [IsProP p P] (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) : product p G ⟶ P
```

**Native source docstring:** The morphism from the free pro-`p` product induced by a family of
continuous homomorphisms to a pro-`p` target.

[Source](../ProfiniteGroups/ProP.lean#L523) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.lift_of

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.lift_of {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} [IsProP p P] (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (i : ι) : (Hom.hom (lift p f)).comp (of p G i) = f i
```

**Native source docstring:** The free pro-`p` product's lift restricts to the requested map on each
factor, via the free profinite product and maximal pro-`p` quotient.

[Source](../ProfiniteGroups/ProP.lean#L528) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.hom_ext

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.hom_ext {ι : Type v} (p : ℕ) {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} (f g : product p G ⟶ P) (h : ∀ (i : ι), (Hom.hom f).comp (of p G i) = (Hom.hom g).comp (of p G i)) : f = g
```

**Native source docstring:** Morphisms from the free pro-`p` product are determined by their
restrictions to the factors.

[Source](../ProfiniteGroups/ProP.lean#L543) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.hom_ext_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.hom_ext_iff {ι : Type v} {p : ℕ} {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} {f g : product p G ⟶ P} : f = g ↔ ∀ (i : ι), (Hom.hom f).comp (of p G i) = (Hom.hom g).comp (of p G i)
```

**Original catalogue explanation (not a Lean docstring):** Morphisms from the free pro-p product agree if and only if their composites with each canonical factor map agree.

[Source](../ProfiniteGroups/ProP.lean#L545) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.lift_comp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.lift_comp {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} [IsProP p P] {Q : ProfiniteGrp.{max u v}} [IsProP p Q] (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (g : P ⟶ Q) : CategoryTheory.CategoryStruct.comp (lift p f) g = lift p fun (i : ι) => (Hom.hom g).comp (f i)
```

**Native source docstring:** The universal lift is natural in the pro-`p` target.

[Source](../ProfiniteGroups/ProP.lean#L557) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.lift_comp_assoc

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.lift_comp_assoc {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} [IsProP p P] {Q : ProfiniteGrp.{max u v}} [IsProP p Q] (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) (g : P ⟶ Q) {Z : ProfiniteGrp.{max u v}} (h : Q ⟶ Z) : CategoryTheory.CategoryStruct.comp (lift p f) (CategoryTheory.CategoryStruct.comp g h) = CategoryTheory.CategoryStruct.comp (lift p fun (i : ι) => (Hom.hom g).comp (f i)) h
```

**Native source docstring:** The universal lift is natural in the pro-`p` target.

[Source](../ProfiniteGroups/ProP.lean#L558) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.homEquiv

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FreeProPProduct.homEquiv {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} [IsProP p P] : (product p G ⟶ P) ≃ ((i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop)
```

**Native source docstring:** Continuous homomorphisms from the free pro-`p` product to a pro-`p` group
are equivalent to families of continuous homomorphisms from its factors.

[Source](../ProfiniteGroups/ProP.lean#L567) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.homEquiv_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.homEquiv_apply {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} [IsProP p P] (f : product p G ⟶ P) (i : ι) : (homEquiv p) f i = (Hom.hom f).comp (of p G i)
```

**Native source docstring:** The forward universal-property correspondence restricts a morphism from
the free pro-`p` product to the indicated factor.

[Source](../ProfiniteGroups/ProP.lean#L579) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.homEquiv_symm_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.homEquiv_symm_apply {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] {G : ι → ProfiniteGrp.{u}} {P : ProfiniteGrp.{max u v}} [IsProP p P] (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑P.toProfinite.toTop) : (homEquiv p).symm f = lift p f
```

**Native source docstring:** The inverse universal-property correspondence extends the family by
`lift p`, with the pro-`p` assumption on its target.

[Source](../ProfiniteGroups/ProP.lean#L585) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.of_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.of_injective {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] (G : ι → ProfiniteGrp.{u}) [∀ (i : ι), IsProP p (G i)] (i : ι) : Function.Injective ⇑(of p G i)
```

**Native source docstring:** If every factor is pro-`p`, each canonical factor map into the free
pro-`p` product is injective.

[Source](../ProfiniteGroups/ProP.lean#L642) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.map

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.FreeProPProduct.map {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] (G : ι → ProfiniteGrp.{u}) {H : ι → ProfiniteGrp.{u}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑(H i).toProfinite.toTop) : product p G ⟶ product p H
```

**Native source docstring:** A family of continuous homomorphisms induces a morphism of free pro-`p`
products.

[Source](../ProfiniteGroups/ProP.lean#L656) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.map_of

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.map_of {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] (G : ι → ProfiniteGrp.{u}) {H : ι → ProfiniteGrp.{u}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑(H i).toProfinite.toTop) (i : ι) : (Hom.hom (map p G f)).comp (of p G i) = (of p H i).comp (f i)
```

**Native source docstring:** The morphism induced by a family of continuous homomorphisms commutes
with each canonical factor map, whether or not the factors are pro-`p`.

[Source](../ProfiniteGroups/ProP.lean#L662) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.map_id

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.map_id {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] (G : ι → ProfiniteGrp.{u}) : (map p G fun (i : ι) => ContinuousMonoidHom.id ↑(G i).toProfinite.toTop) = CategoryTheory.CategoryStruct.id (product p G)
```

**Native source docstring:** Identity maps on all factors induce the identity of their free pro-`p`
product.

[Source](../ProfiniteGroups/ProP.lean#L669) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.FreeProPProduct.map_comp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.FreeProPProduct.map_comp {ι : Type v} (p : ℕ) [Fact (Nat.Prime p)] (G : ι → ProfiniteGrp.{u}) {H K : ι → ProfiniteGrp.{u}} (f : (i : ι) → ↑(G i).toProfinite.toTop →ₜ* ↑(H i).toProfinite.toTop) (g : (i : ι) → ↑(H i).toProfinite.toTop →ₜ* ↑(K i).toProfinite.toTop) : CategoryTheory.CategoryStruct.comp (map p G f) (map p H g) = map p G fun (i : ι) => (g i).comp (f i)
```

**Native source docstring:** Mapping free pro-`p` products twice agrees with mapping the componentwise
composites of the factor homomorphisms.

[Source](../ProfiniteGroups/ProP.lean#L679) (native source start line; generated entries may point to their parent).

#### Native instance table

- `ProfiniteGrp.FreeProPProduct.product_isProP`: `ProfiniteGrp.IsProP`; type names: `ProfiniteGrp.FreeProPProduct.product`

- `ProfiniteGrp.MaximalProPQuotient.Quotient.instNonempty`: `Nonempty`; type names: `ProfiniteGrp.MaximalProPQuotient.Quotient`

- `ProfiniteGrp.MaximalProPQuotient.Quotient.instOrderTop`: `OrderTop`; type names: `ProfiniteGrp.MaximalProPQuotient.Quotient`

- `ProfiniteGrp.MaximalProPQuotient.Quotient.instPartialOrder`: `PartialOrder`; type names: `ProfiniteGrp.MaximalProPQuotient.Quotient`

- `ProfiniteGrp.MaximalProPQuotient.Quotient.instSemilatticeInf`: `SemilatticeInf`; type names: `ProfiniteGrp.MaximalProPQuotient.Quotient`

- `ProfiniteGrp.MaximalProPQuotient.product_isProP`: `ProfiniteGrp.IsProP`; type names: `ProfiniteGrp.MaximalProPQuotient.product`

### ProfiniteGroups.Procyclic

44 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.IsTopologicalGenerator

Kind: `def`.

```lean
def ProfiniteGrp.IsTopologicalGenerator (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : Prop
```

**Native source docstring:** An element of a profinite group is a topological generator when its integral
powers have dense range.

[Source](../ProfiniteGroups/Procyclic.lean#L31) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProcyclic

Kind: `def`.

```lean
def ProfiniteGrp.IsProcyclic (G : ProfiniteGrp.{u}) : Prop
```

**Native source docstring:** A profinite group is procyclic when it has a topological generator.

[Source](../ProfiniteGroups/Procyclic.lean#L36) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsTopologicalGenerator.iff_topologicalClosure_zpowers

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsTopologicalGenerator.iff_topologicalClosure_zpowers {G : ProfiniteGrp.{u}} {g : ↑G.toProfinite.toTop} : G.IsTopologicalGenerator g ↔ (Subgroup.zpowers g).topologicalClosure = ⊤
```

**Native source docstring:** Topological generation expressed using the closure of the cyclic subgroup.

[Source](../ProfiniteGroups/Procyclic.lean#L44) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsTopologicalGenerator.iff_closure_range

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsTopologicalGenerator.iff_closure_range {G : ProfiniteGrp.{u}} {g : ↑G.toProfinite.toTop} : G.IsTopologicalGenerator g ↔ closure (Set.range fun (n : ℤ) => g ^ n) = Set.univ
```

**Native source docstring:** Topological generation expressed directly as a closure equality.

[Source](../ProfiniteGroups/Procyclic.lean#L51) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsTopologicalGenerator.denseRange_pow

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsTopologicalGenerator.denseRange_pow {G : ProfiniteGrp.{u}} {g : ↑G.toProfinite.toTop} (hg : G.IsTopologicalGenerator g) : DenseRange fun (n : ℕ) => g ^ n
```

**Native source docstring:** The natural powers of a topological generator are also dense.

[Source](../ProfiniteGroups/Procyclic.lean#L56) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsTopologicalGenerator.map

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsTopologicalGenerator.map {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} {g : ↑G.toProfinite.toTop} (hg : G.IsTopologicalGenerator g) (f : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop) (hf : Function.Surjective ⇑f) : H.IsTopologicalGenerator (f g)
```

**Native source docstring:** A surjective continuous homomorphism sends a topological generator to a
topological generator.

[Source](../ProfiniteGroups/Procyclic.lean#L61) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsTopologicalGenerator.map_equiv

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsTopologicalGenerator.map_equiv {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} {g : ↑G.toProfinite.toTop} (hg : G.IsTopologicalGenerator g) (e : ↑G.toProfinite.toTop ≃ₜ* ↑H.toProfinite.toTop) : H.IsTopologicalGenerator (e g)
```

**Native source docstring:** A continuous group equivalence preserves topological generators.

[Source](../ProfiniteGroups/Procyclic.lean#L73) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsTopologicalGenerator.equiv_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsTopologicalGenerator.equiv_iff {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} {g : ↑G.toProfinite.toTop} (e : ↑G.toProfinite.toTop ≃ₜ* ↑H.toProfinite.toTop) : H.IsTopologicalGenerator (e g) ↔ G.IsTopologicalGenerator g
```

**Native source docstring:** A continuous group equivalence reflects topological generators.

[Source](../ProfiniteGroups/Procyclic.lean#L78) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isTopologicalGenerator_of_subsingleton

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isTopologicalGenerator_of_subsingleton (G : ProfiniteGrp.{u}) [Subsingleton ↑G.toProfinite.toTop] (g : ↑G.toProfinite.toTop) : G.IsTopologicalGenerator g
```

**Native source docstring:** Every element of a subsingleton profinite group is a topological generator.

[Source](../ProfiniteGroups/Procyclic.lean#L88) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isProcyclic_of_subsingleton

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isProcyclic_of_subsingleton (G : ProfiniteGrp.{u}) [Subsingleton ↑G.toProfinite.toTop] : G.IsProcyclic
```

**Native source docstring:** Every subsingleton profinite group is procyclic.

[Source](../ProfiniteGroups/Procyclic.lean#L95) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.punit_isProcyclic

Kind: `theorem`.

```lean
theorem ProfiniteGrp.punit_isProcyclic : (ofFiniteGrp ↧PUnit.{u_1 + 1}).IsProcyclic
```

**Native source docstring:** The standard one-element profinite group is procyclic.

[Source](../ProfiniteGroups/Procyclic.lean#L100) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isProcyclic_iff_of_continuousMulEquiv

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isProcyclic_iff_of_continuousMulEquiv (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (e : ↑G.toProfinite.toTop ≃ₜ* ↑H.toProfinite.toTop) : G.IsProcyclic ↔ H.IsProcyclic
```

**Native source docstring:** Procyclicity is preserved and reflected by a continuous group equivalence.

[Source](../ProfiniteGroups/Procyclic.lean#L108) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProcyclic.quotient

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProcyclic.quotient {G H : ProfiniteGrp.{u}} (hG : G.IsProcyclic) (f : G ⟶ H) (hf : Function.Surjective ⇑(Hom.hom f)) : H.IsProcyclic
```

**Native source docstring:** A continuous quotient of a procyclic profinite group is procyclic.

[Source](../ProfiniteGroups/Procyclic.lean#L117) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletion

Kind: `def`.

```lean
abbrev ProfiniteGrp.integerCompletion : ProfiniteGrp.{u}
```

**Native source docstring:** The profinite completion of the infinite cyclic group, in any target
universe.

[Source](../ProfiniteGroups/Procyclic.lean#L123) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerPowerHom

Kind: `def`.

```lean
def ProfiniteGrp.integerPowerHom (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : ↧(ULift.{u, 0} (Multiplicative ℤ)) ⟶ ↧↑G.toProfinite.toTop
```

**Native source docstring:** The homomorphism from the infinite cyclic group determined by `g`.

[Source](../ProfiniteGroups/Procyclic.lean#L128) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionMap

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.integerCompletionMap (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : integerCompletion ⟶ G
```

**Native source docstring:** The canonical continuous homomorphism from the profinite completion of the
integers which sends `1` to `g`.

[Source](../ProfiniteGroups/Procyclic.lean#L133) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionMap_eta

Kind: `theorem`.

```lean
theorem ProfiniteGrp.integerCompletionMap_eta (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (n : ULift.{u, 0} (Multiplicative ℤ)) : (Hom.hom (G.integerCompletionMap g)) (ProfiniteCompletion.etaFn (↧(ULift.{u, 0} (Multiplicative ℤ))) n) = g ^ Multiplicative.toAdd n.down
```

**Native source docstring:** The canonical completion map extends integral exponentiation.

[Source](../ProfiniteGroups/Procyclic.lean#L139) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.integerCompletionMap_eta_int

Kind: `theorem`.

```lean
theorem ProfiniteGrp.integerCompletionMap_eta_int (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (n : ℤ) : (Hom.hom (G.integerCompletionMap g)) (ProfiniteCompletion.etaFn ↧(ULift.{u, 0} (Multiplicative ℤ)) { down := Multiplicative.ofAdd n }) = g ^ n
```

**Native source docstring:** The value of the canonical completion map on the usual integral dense
subgroup.

[Source](../ProfiniteGroups/Procyclic.lean#L156) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.closure_range_integerCompletionMap

Kind: `theorem`.

```lean
theorem ProfiniteGrp.closure_range_integerCompletionMap (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : closure (Set.range ⇑(Hom.hom (G.integerCompletionMap g))) = closure (Set.range fun (n : ℤ) => g ^ n)
```

**Native source docstring:** The closure of the range of the canonical completion map is the closure of
the integral powers of its distinguished element.

[Source](../ProfiniteGroups/Procyclic.lean#L165) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.range_integerCompletionMap

Kind: `theorem`.

```lean
theorem ProfiniteGrp.range_integerCompletionMap (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : Set.range ⇑(Hom.hom (G.integerCompletionMap g)) = closure (Set.range fun (n : ℤ) => g ^ n)
```

**Native source docstring:** The range of the canonical completion map is exactly the closure of the
integral powers.  Closedness here uses compactness of the completion and the
Hausdorff topology on the target.

[Source](../ProfiniteGroups/Procyclic.lean#L196) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isTopologicalGenerator_iff_surjective_integerCompletionMap

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isTopologicalGenerator_iff_surjective_integerCompletionMap (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : G.IsTopologicalGenerator g ↔ Function.Surjective ⇑(Hom.hom (G.integerCompletionMap g))
```

**Native source docstring:** An element topologically generates exactly when its canonical map from the
profinite completion of the integers is surjective.

[Source](../ProfiniteGroups/Procyclic.lean#L205) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isTopologicalGenerator_iff_epi_integerCompletionMap

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isTopologicalGenerator_iff_epi_integerCompletionMap (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : G.IsTopologicalGenerator g ↔ CategoryTheory.Epi (G.integerCompletionMap g)
```

**Native source docstring:** The categorical form of the completion-map characterization.

[Source](../ProfiniteGroups/Procyclic.lean#L214) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isProcyclic_iff_exists_surjective_integerCompletionMap

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isProcyclic_iff_exists_surjective_integerCompletionMap (G : ProfiniteGrp.{u}) : G.IsProcyclic ↔ ∃ (g : ↑G.toProfinite.toTop), Function.Surjective ⇑(Hom.hom (G.integerCompletionMap g))
```

**Native source docstring:** A profinite group is procyclic exactly when one of its canonical maps from
the profinite completion of the integers is surjective.

[Source](../ProfiniteGroups/Procyclic.lean#L221) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.finiteCyclic

Kind: `def`.

```lean
abbrev ProfiniteGrp.finiteCyclic (n : ℕ) [NeZero n] : ProfiniteGrp.{0}
```

**Native source docstring:** The standard finite cyclic profinite group of order `n`.

[Source](../ProfiniteGroups/Procyclic.lean#L229) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.finiteCyclicGenerator

Kind: `def`.

```lean
abbrev ProfiniteGrp.finiteCyclicGenerator (n : ℕ) [NeZero n] : ↑(finiteCyclic n).toProfinite.toTop
```

**Native source docstring:** The standard generator of `finiteCyclic n`.

[Source](../ProfiniteGroups/Procyclic.lean#L233) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.finiteCyclicGenerator_isTopologicalGenerator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.finiteCyclicGenerator_isTopologicalGenerator (n : ℕ) [NeZero n] : (finiteCyclic n).IsTopologicalGenerator (finiteCyclicGenerator n)
```

**Native source docstring:** The standard generator topologically generates the finite cyclic profinite
group.

[Source](../ProfiniteGroups/Procyclic.lean#L237) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.finiteCyclic_isProcyclic

Kind: `theorem`.

```lean
theorem ProfiniteGrp.finiteCyclic_isProcyclic (n : ℕ) [NeZero n] : (finiteCyclic n).IsProcyclic
```

**Native source docstring:** Every standard finite cyclic profinite group is procyclic.

[Source](../ProfiniteGroups/Procyclic.lean#L250) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.IsTopologicalGenerator

Kind: `def`.

```lean
def ProfiniteAddGrp.IsTopologicalGenerator (G : ProfiniteAddGrp.{u}) (g : ↑G.toProfinite.toTop) : Prop
```

**Native source docstring:** An element of a profinite additive group is a topological generator when
its integral multiples have dense range.

[Source](../ProfiniteGroups/Procyclic.lean#L258) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.IsProcyclic

Kind: `def`.

```lean
def ProfiniteAddGrp.IsProcyclic (G : ProfiniteAddGrp.{u}) : Prop
```

**Native source docstring:** A profinite additive group is procyclic when it has a topological
generator.

[Source](../ProfiniteGroups/Procyclic.lean#L263) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.IsTopologicalGenerator.iff_topologicalClosure_zmultiples

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.IsTopologicalGenerator.iff_topologicalClosure_zmultiples {G : ProfiniteAddGrp.{u}} {g : ↑G.toProfinite.toTop} : G.IsTopologicalGenerator g ↔ (AddSubgroup.zmultiples g).topologicalClosure = ⊤
```

**Native source docstring:** Additive topological generation expressed using the closure of the cyclic
additive subgroup.

[Source](../ProfiniteGroups/Procyclic.lean#L272) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.IsTopologicalGenerator.iff_closure_range

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.IsTopologicalGenerator.iff_closure_range {G : ProfiniteAddGrp.{u}} {g : ↑G.toProfinite.toTop} : G.IsTopologicalGenerator g ↔ closure (Set.range fun (n : ℤ) => n • g) = Set.univ
```

**Native source docstring:** Additive topological generation expressed directly as a closure equality.

[Source](../ProfiniteGroups/Procyclic.lean#L281) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.IsTopologicalGenerator.denseRange_nsmul

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.IsTopologicalGenerator.denseRange_nsmul {G : ProfiniteAddGrp.{u}} {g : ↑G.toProfinite.toTop} (hg : G.IsTopologicalGenerator g) : DenseRange fun (n : ℕ) => n • g
```

**Native source docstring:** The natural multiples of an additive topological generator are dense.

[Source](../ProfiniteGroups/Procyclic.lean#L286) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.IsTopologicalGenerator.map

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.IsTopologicalGenerator.map {G : ProfiniteAddGrp.{u}} {H : ProfiniteAddGrp.{v}} {g : ↑G.toProfinite.toTop} (hg : G.IsTopologicalGenerator g) (f : ↑G.toProfinite.toTop →ₜ+ ↑H.toProfinite.toTop) (hf : Function.Surjective ⇑f) : H.IsTopologicalGenerator (f g)
```

**Native source docstring:** A surjective continuous additive homomorphism sends a topological generator
to a topological generator.

[Source](../ProfiniteGroups/Procyclic.lean#L291) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.IsTopologicalGenerator.map_equiv

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.IsTopologicalGenerator.map_equiv {G : ProfiniteAddGrp.{u}} {H : ProfiniteAddGrp.{v}} {g : ↑G.toProfinite.toTop} (hg : G.IsTopologicalGenerator g) (e : ↑G.toProfinite.toTop ≃ₜ+ ↑H.toProfinite.toTop) : H.IsTopologicalGenerator (e g)
```

**Native source docstring:** A continuous additive equivalence preserves topological generators.

[Source](../ProfiniteGroups/Procyclic.lean#L303) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.IsTopologicalGenerator.equiv_iff

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.IsTopologicalGenerator.equiv_iff {G : ProfiniteAddGrp.{u}} {H : ProfiniteAddGrp.{v}} {g : ↑G.toProfinite.toTop} (e : ↑G.toProfinite.toTop ≃ₜ+ ↑H.toProfinite.toTop) : H.IsTopologicalGenerator (e g) ↔ G.IsTopologicalGenerator g
```

**Native source docstring:** A continuous additive equivalence reflects topological generators.

[Source](../ProfiniteGroups/Procyclic.lean#L308) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.isTopologicalGenerator_of_subsingleton

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.isTopologicalGenerator_of_subsingleton (G : ProfiniteAddGrp.{u}) [Subsingleton ↑G.toProfinite.toTop] (g : ↑G.toProfinite.toTop) : G.IsTopologicalGenerator g
```

**Native source docstring:** Every element of a subsingleton profinite additive group is a topological
generator.

[Source](../ProfiniteGroups/Procyclic.lean#L318) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.isProcyclic_of_subsingleton

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.isProcyclic_of_subsingleton (G : ProfiniteAddGrp.{u}) [Subsingleton ↑G.toProfinite.toTop] : G.IsProcyclic
```

**Native source docstring:** Every subsingleton profinite additive group is procyclic.

[Source](../ProfiniteGroups/Procyclic.lean#L326) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.punit_isProcyclic

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.punit_isProcyclic : (ofFiniteAddGrp ↧PUnit.{u_1 + 1}).IsProcyclic
```

**Native source docstring:** The standard one-element profinite additive group is procyclic.

[Source](../ProfiniteGroups/Procyclic.lean#L331) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.isProcyclic_iff_of_continuousAddEquiv

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.isProcyclic_iff_of_continuousAddEquiv (G : ProfiniteAddGrp.{u}) (H : ProfiniteAddGrp.{v}) (e : ↑G.toProfinite.toTop ≃ₜ+ ↑H.toProfinite.toTop) : G.IsProcyclic ↔ H.IsProcyclic
```

**Native source docstring:** Additive procyclicity is preserved and reflected by a continuous additive
equivalence.

[Source](../ProfiniteGroups/Procyclic.lean#L339) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.IsProcyclic.quotient

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.IsProcyclic.quotient {G H : ProfiniteAddGrp.{u}} (hG : G.IsProcyclic) (f : G ⟶ H) (hf : Function.Surjective ⇑(Hom.hom f)) : H.IsProcyclic
```

**Native source docstring:** A continuous quotient of a procyclic profinite additive group is
procyclic.

[Source](../ProfiniteGroups/Procyclic.lean#L349) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.finiteCyclic

Kind: `def`.

```lean
abbrev ProfiniteAddGrp.finiteCyclic (n : ℕ) [NeZero n] : ProfiniteAddGrp.{0}
```

**Native source docstring:** The standard finite cyclic profinite additive group of order `n`.

[Source](../ProfiniteGroups/Procyclic.lean#L356) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.finiteCyclicGenerator

Kind: `def`.

```lean
abbrev ProfiniteAddGrp.finiteCyclicGenerator (n : ℕ) [NeZero n] : ↑(finiteCyclic n).toProfinite.toTop
```

**Native source docstring:** The standard generator of the additive `finiteCyclic n`.

[Source](../ProfiniteGroups/Procyclic.lean#L360) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.finiteCyclicGenerator_isTopologicalGenerator

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.finiteCyclicGenerator_isTopologicalGenerator (n : ℕ) [NeZero n] : (finiteCyclic n).IsTopologicalGenerator (finiteCyclicGenerator n)
```

**Native source docstring:** The standard additive generator topologically generates the finite cyclic
profinite additive group.

[Source](../ProfiniteGroups/Procyclic.lean#L364) (native source start line; generated entries may point to their parent).

#### ProfiniteAddGrp.finiteCyclic_isProcyclic

Kind: `theorem`.

```lean
theorem ProfiniteAddGrp.finiteCyclic_isProcyclic (n : ℕ) [NeZero n] : (finiteCyclic n).IsProcyclic
```

**Native source docstring:** Every standard finite cyclic profinite additive group is procyclic.

[Source](../ProfiniteGroups/Procyclic.lean#L378) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.ProcyclicBaseMap

12 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.primeFact

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primeFact (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Native source docstring:** Primality for the p-adic coordinate indexed by a prime.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L26) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicChangeUniverse

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicChangeUniverse : ↑primewisePadic.toProfinite.toTop ≃ₜ* ↑primewisePadic.toProfinite.toTop
```

**Native source docstring:** Change the universe of each p-adic coordinate without changing its value.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L29) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicChangeUniverse_apply_down

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicChangeUniverse_apply_down (x : ↑primewisePadic.toProfinite.toTop) (p : Nat.Primes) : (Multiplicative.toAdd (primewisePadicChangeUniverse x p)).down = (Multiplicative.toAdd (x p)).down
```

**Native source docstring:** Universe change preserves the ordinary p-adic value at every prime.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L43) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicChangeUniverse_diagonal

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicChangeUniverse_diagonal (n : ℤ) : primewisePadicChangeUniverse (primewisePadicDiagonal n) = primewisePadicDiagonal n
```

**Native source docstring:** The primewise integer diagonal commutes with universe change.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L50) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicChangeUniverse_generator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicChangeUniverse_generator : primewisePadicChangeUniverse primewisePadicGenerator = primewisePadicGenerator
```

**Native source docstring:** Universe change carries the canonical topological generator to itself.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L62) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicChangeUniverse_self

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicChangeUniverse_self : primewisePadicChangeUniverse = ContinuousMulEquiv.refl ↑primewisePadic.toProfinite.toTop
```

**Native source docstring:** Changing universe to itself gives the identity.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L69) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicChangeUniverse_symm

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicChangeUniverse_symm : primewisePadicChangeUniverse.symm = primewisePadicChangeUniverse
```

**Native source docstring:** Reversing universe change gives its inverse.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L80) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicChangeUniverse_trans

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicChangeUniverse_trans : primewisePadicChangeUniverse.trans primewisePadicChangeUniverse = primewisePadicChangeUniverse
```

**Native source docstring:** Successive changes of universe agree with direct change.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L94) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicBaseMapOfGenerator

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicBaseMapOfGenerator (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : ↑primewisePadic.toProfinite.toTop →ₜ* ↑G.toProfinite.toTop
```

**Native source docstring:** The map from the universe-zero primewise product determined by an arbitrary
element of a profinite group. It need not be surjective.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L106) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicBaseMapOfGenerator_diagonal

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicBaseMapOfGenerator_diagonal (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (n : ℤ) : (G.primewisePadicBaseMapOfGenerator g) (primewisePadicDiagonal n) = g ^ n
```

**Native source docstring:** The common-source map takes the integer diagonal to powers of its element.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L113) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicBaseMapOfGenerator_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicBaseMapOfGenerator_surjective (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : Function.Surjective ⇑(G.primewisePadicBaseMapOfGenerator g)
```

**Native source docstring:** A topological generator yields a surjection from the common source.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L120) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicBaseMapOfGenerator_naturality

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicBaseMapOfGenerator_naturality (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (f : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop) (g : ↑G.toProfinite.toTop) : f.comp (G.primewisePadicBaseMapOfGenerator g) = H.primewisePadicBaseMapOfGenerator (f g)
```

**Native source docstring:** The common-source maps are natural under arbitrary continuous homomorphisms,
without generation, injectivity or surjectivity assumptions.

[Source](../ProfiniteGroups/ProcyclicBaseMap.lean#L127) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.ProcyclicGeneratorIndependence

4 native named entries; 0 native instance-table rows.

#### AddMonoidHom.ker_eq_of_surjective_dense_intCast

Kind: `theorem`.

```lean
theorem AddMonoidHom.ker_eq_of_surjective_dense_intCast {R : Type u} {A : Type v} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [AddGroup A] [TopologicalSpace A] [T2Space A] (dense : DenseRange fun (n : ℤ) => ↑n) (f h : R →+ A) (cf : Continuous ⇑f) (ch : Continuous ⇑h) (sf : Function.Surjective ⇑f) (sh : Function.Surjective ⇑h) : f.ker = h.ker
```

**Native source docstring:** Two continuous surjective additive maps from a topological ring with dense
integer casts to the same Hausdorff additive group have identical kernels.
Neither ring commutativity nor a topological group structure on the target is
required. The maps themselves need not be equal.

[Source](../ProfiniteGroups/ProcyclicGeneratorIndependence.lean#L31) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdeal_eq_of_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdeal_eq_of_surjective {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y] (f h : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (sf : Function.Surjective ⇑f) (sh : Function.Surjective ⇑h) : primewisePadicKernelIdeal f = primewisePadicKernelIdeal h
```

**Native source docstring:** Continuous surjections from the primewise p-adic product onto the same
Hausdorff group have equal kernel ideals; the maps need not coincide.

[Source](../ProfiniteGroups/ProcyclicGeneratorIndependence.lean#L75) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdeal_mapOfGenerator_eq

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdeal_mapOfGenerator_eq (G : ProfiniteGrp.{u}) (g h : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (hh : G.IsTopologicalGenerator h) : primewisePadicKernelIdeal (G.primewisePadicMapOfGenerator g) = primewisePadicKernelIdeal (G.primewisePadicMapOfGenerator h)
```

**Native source docstring:** The kernel ideal of the primewise map determined by a topological
generator is independent of which topological generator is supplied.

[Source](../ProfiniteGroups/ProcyclicGeneratorIndependence.lean#L106) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicExponentsOfGenerator_eq

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicExponentsOfGenerator_eq (G : ProfiniteGrp.{u}) (g h : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (hh : G.IsTopologicalGenerator h) : G.primewisePadicExponentsOfGenerator g = G.primewisePadicExponentsOfGenerator h
```

**Native source docstring:** The primewise exponent family of a procyclic profinite group is
independent of its supplied topological generator.

[Source](../ProfiniteGroups/ProcyclicGeneratorIndependence.lean#L118) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.ProcyclicHom

15 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.continuousHom_ext_of_generator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.continuousHom_ext_of_generator {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} {g : ↑G.toProfinite.toTop} (hg : G.IsTopologicalGenerator g) (f k : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop) (h : f g = k g) : f = k
```

**Native source docstring:** Continuous homomorphisms out of a procyclic group agree if they agree on a
supplied topological generator.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L30) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.continuousHomLiftOfSurjective

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.continuousHomLiftOfSurjective {A : ProfiniteGrp.{w}} {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (q : ↑A.toProfinite.toTop →ₜ* ↑G.toProfinite.toTop) (r : ↑A.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop) (hq : Function.Surjective ⇑q) (hker : q.ker ≤ r.ker) : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop
```

**Native source docstring:** A continuous surjection from a compact group factors any continuous
homomorphism whose kernel contains its kernel, continuously and uniquely.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L48) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.continuousHomLiftOfSurjective_comp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.continuousHomLiftOfSurjective_comp {A : ProfiniteGrp.{w}} {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (q : ↑A.toProfinite.toTop →ₜ* ↑G.toProfinite.toTop) (r : ↑A.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop) (hq : Function.Surjective ⇑q) (hker : q.ker ≤ r.ker) : (continuousHomLiftOfSurjective q r hq hker).comp q = r
```

**Native source docstring:** The quotient-map lift commutes with its surjective input. The kernel
inclusion is the condition that makes the descended map well-defined.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L68) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.baseMap_kernel_le_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.baseMap_kernel_le_iff {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (g : ↑G.toProfinite.toTop) (h : ↑H.toProfinite.toTop) : (G.primewisePadicBaseMapOfGenerator g).ker ≤ (H.primewisePadicBaseMapOfGenerator h).ker ↔ ∀ (p : Nat.Primes), primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ primewisePadicKernelExponents (G.primewisePadicBaseMapOfGenerator g) p
```

**Native source docstring:** Inclusion of the kernels of common-source maps is precisely reversed
pointwise comparison of their primewise kernel exponents.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L84) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.baseMap_kernel_le_iff_exponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.baseMap_kernel_le_iff_exponents {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) : (G.primewisePadicBaseMapOfGenerator g).ker ≤ (H.primewisePadicBaseMapOfGenerator h).ker ↔ ∀ (p : Nat.Primes), primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p
```

**Native source docstring:** The generator-independent exponent condition for mapping `g` to `h`.
It makes no generation assumption about the target.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L113) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.factorOfGenerator

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.factorOfGenerator {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) (hadmissible : ∀ (p : Nat.Primes), primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p) : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop
```

**Native source docstring:** The canonical continuous homomorphism with prescribed value on `g`.
The required inequality is a genuine existence condition, not a condition for
mere existence of some homomorphism.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L124) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.factorOfGenerator_comp_baseMap

Kind: `theorem`.

```lean
theorem ProfiniteGrp.factorOfGenerator_comp_baseMap {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) (hadmissible : ∀ (p : Nat.Primes), primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p) : (factorOfGenerator hG g hg h hadmissible).comp (G.primewisePadicBaseMapOfGenerator g) = H.primewisePadicBaseMapOfGenerator h
```

**Native source docstring:** The factor prescribed by an image of the generator commutes with both
primewise common-source maps.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L137) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.factorOfGenerator_apply_generator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.factorOfGenerator_apply_generator {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) (hadmissible : ∀ (p : Nat.Primes), primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p) : (factorOfGenerator hG g hg h hadmissible) g = h
```

**Native source docstring:** The descended factor really takes the supplied source generator to its
prescribed value in the possibly nonprocyclic target.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L149) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.existsUnique_continuousHom_apply_generator_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.existsUnique_continuousHom_apply_generator_iff {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) : (∃! f : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop, f g = h) ↔ ∀ (p : Nat.Primes), primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p
```

**Native source docstring:** Evaluation at a generator has a unique prescribed inverse value exactly
when the common-source kernel exponents satisfy the pointwise condition.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L165) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.factorOfGenerator_surjective_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.factorOfGenerator_surjective_iff {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) (hadmissible : ∀ (p : Nat.Primes), primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p) : Function.Surjective ⇑(factorOfGenerator hG g hg h hadmissible) ↔ H.IsTopologicalGenerator h
```

**Native source docstring:** The canonical factor is onto exactly when its prescribed image generates
the entire target.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L192) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.exists_surjective_continuousHom_iff_exponents_le

Kind: `theorem`.

```lean
theorem ProfiniteGrp.exists_surjective_continuousHom_iff_exponents_le {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (hH : H.IsProcyclic) : (∃ (f : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop), Function.Surjective ⇑f) ↔ ∀ (p : Nat.Primes), hH.exponents p ≤ hG.exponents p
```

**Native source docstring:** A continuous quotient between procyclic profinite groups exists exactly
when the exponents of the target are bounded by those of the source.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L212) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.factorOfGenerator_self

Kind: `theorem`.

```lean
theorem ProfiniteGrp.factorOfGenerator_self {G : ProfiniteGrp.{u}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (hadmissible : ∀ (p : Nat.Primes), primewisePadicKernelExponents (G.primewisePadicBaseMapOfGenerator g) p ≤ hG.exponents p) : factorOfGenerator hG g hg g hadmissible = ContinuousMonoidHom.id ↑G.toProfinite.toTop
```

**Native source docstring:** The factor assigning the source generator to itself is the identity.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L237) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.one_admissible

Kind: `theorem`.

```lean
theorem ProfiniteGrp.one_admissible {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (p : Nat.Primes) : primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator 1) p ≤ hG.exponents p
```

**Native source docstring:** The identity element is always an admissible image of a generator.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L245) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.factorOfGenerator_one

Kind: `theorem`.

```lean
theorem ProfiniteGrp.factorOfGenerator_one {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : factorOfGenerator hG g hg 1 ⋯ = 1
```

**Native source docstring:** Sending a topological generator to the identity gives the trivial map.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L255) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.factorOfGenerator_comp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.factorOfGenerator_comp {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} {K : ProfiniteGrp.{w}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (hH : H.IsProcyclic) (h : ↑H.toProfinite.toTop) (hh : H.IsTopologicalGenerator h) (k : ↑K.toProfinite.toTop) (ha : ∀ (p : Nat.Primes), primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p) (hb : ∀ (p : Nat.Primes), primewisePadicKernelExponents (K.primewisePadicBaseMapOfGenerator k) p ≤ hH.exponents p) : (factorOfGenerator hH h hh k hb).comp (factorOfGenerator hG g hg h ha) = factorOfGenerator hG g hg k ⋯
```

**Native source docstring:** Composing two canonical factors agrees with evaluation at the source
generator, whenever the resulting prescribed image is admissible.

[Source](../ProfiniteGroups/ProcyclicHom.lean#L261) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.ProcyclicInvariant

9 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.primewisePadicKernelIdeal_comp_injective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdeal_comp_injective {Y : Type v} {Z : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y] [Group Z] [TopologicalSpace Z] [T1Space Z] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (j : Y →ₜ* Z) (hj : Function.Injective ⇑j) : primewisePadicKernelIdeal (j.comp f) = primewisePadicKernelIdeal f
```

**Native source docstring:** Postcomposition by an injective continuous homomorphism preserves the
actual primewise p-adic kernel ideal, with no surjectivity assumption.

[Source](../ProfiniteGroups/ProcyclicInvariant.lean#L30) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProcyclic.exponents

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.IsProcyclic.exponents {G : ProfiniteGrp.{u}} (hG : G.IsProcyclic) : Nat.Primes → ℕ∞
```

**Native source docstring:** The primewise exponents of a procyclic profinite group, formed using a
chosen generator and the fixed universe-zero p-adic source. Independent of
the chosen generator by `exponents_eq_of_generator`.

[Source](../ProfiniteGroups/ProcyclicInvariant.lean#L46) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProcyclic.baseMap_exponents_eq_of_generators

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProcyclic.baseMap_exponents_eq_of_generators (G : ProfiniteGrp.{u}) (g h : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (hh : G.IsTopologicalGenerator h) : primewisePadicKernelExponents (G.primewisePadicBaseMapOfGenerator g) = primewisePadicKernelExponents (G.primewisePadicBaseMapOfGenerator h)
```

**Native source docstring:** The fixed-base exponent family does not depend on the supplied
topological generator.

[Source](../ProfiniteGroups/ProcyclicInvariant.lean#L53) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProcyclic.exponents_eq_baseMap_of_generator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProcyclic.exponents_eq_baseMap_of_generator {G : ProfiniteGrp.{u}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : hG.exponents = primewisePadicKernelExponents (G.primewisePadicBaseMapOfGenerator g)
```

**Native source docstring:** The invariant agrees with the fixed-base kernel exponent family for
any actual topological generator.

[Source](../ProfiniteGroups/ProcyclicInvariant.lean#L67) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProcyclic.exponents_eq_of_generator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProcyclic.exponents_eq_of_generator {G : ProfiniteGrp.{u}} (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : hG.exponents = G.primewisePadicExponentsOfGenerator g
```

**Native source docstring:** Any supplied generator computes the invariant using the original
generator-dependent exponent family.

[Source](../ProfiniteGroups/ProcyclicInvariant.lean#L76) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProcyclic.exponents_eq

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProcyclic.exponents_eq {G : ProfiniteGrp.{u}} (hG hG' : G.IsProcyclic) : hG.exponents = hG'.exponents
```

**Native source docstring:** The exponent family is independent of the proof of procyclicity.

[Source](../ProfiniteGroups/ProcyclicInvariant.lean#L85) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProcyclic.exponents_equiv

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProcyclic.exponents_equiv {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} (hG : G.IsProcyclic) (hH : H.IsProcyclic) (e : ↑G.toProfinite.toTop ≃ₜ* ↑H.toProfinite.toTop) : hG.exponents = hH.exponents
```

**Native source docstring:** An equivalence of procyclic profinite groups preserves their exponents,
even when the groups live in different universes.

[Source](../ProfiniteGroups/ProcyclicInvariant.lean#L92) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.IsProcyclic.continuousMulEquivModel

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.IsProcyclic.continuousMulEquivModel {G : ProfiniteGrp.{u}} (hG : G.IsProcyclic) : ↑G.toProfinite.toTop ≃ₜ* Multiplicative ↑(primewisePadicQuotientModel hG.exponents).toProfinite.toTop
```

**Native source docstring:** A procyclic group is modeled by the quotient product for its
generator-independent exponents. The equivalence is noncomputable because
selecting a generator and constructing the quotient model use choice.

[Source](../ProfiniteGroups/ProcyclicInvariant.lean#L120) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (hG : G.IsProcyclic) (hH : H.IsProcyclic) : Nonempty (↑G.toProfinite.toTop ≃ₜ* ↑H.toProfinite.toTop) ↔ hG.exponents = hH.exponents
```

**Native source docstring:** Two already-procyclic profinite groups, in possibly different universes,
are topologically multiplicatively equivalent if and only if their
generator-independent exponent families coincide.

[Source](../ProfiniteGroups/ProcyclicInvariant.lean#L132) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.ProcyclicPower

30 native named entries; 1 native instance-table rows.

#### ProfiniteGrp.IsProcyclic.isMulCommutative

Kind: `theorem`.

```lean
theorem ProfiniteGrp.IsProcyclic.isMulCommutative {G : ProfiniteGrp.{u}} (hG : G.IsProcyclic) : IsMulCommutative ↑G.toProfinite.toTop
```

**Native source docstring:** The multiplication of a procyclic profinite group is commutative. No
alternative group structure is installed on the underlying type.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L49) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerHom

Kind: `def`.

```lean
def ProfiniteGrp.powerHom (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) : ↑G.toProfinite.toTop →ₜ* ↑G.toProfinite.toTop
```

**Native source docstring:** The continuous homomorphism that really sends `x` to `x ^ n`.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L69) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerHom_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerHom_apply (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (x : ↑G.toProfinite.toTop) : (G.powerHom hG n) x = x ^ n
```

**Native source docstring:** Evaluation of the continuous power homomorphism is the ordinary natural
power in the original group, with no change of its group structure.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L79) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerHom_zero

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerHom_zero (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (x : ↑G.toProfinite.toTop) : (G.powerHom hG 0) x = 1
```

**Native source docstring:** The zeroth power endomorphism is the constant identity map.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L84) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerHom_one

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerHom_one (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (x : ↑G.toProfinite.toTop) : (G.powerHom hG 1) x = x
```

**Native source docstring:** The first power endomorphism is the identity map.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L88) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerHom_comp

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerHom_comp (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (m n : ℕ) : (G.powerHom hG m).comp (G.powerHom hG n) = G.powerHom hG (n * m)
```

**Native source docstring:** Composition of power endomorphisms is multiplication of exponents.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L92) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage

Kind: `def`.

```lean
def ProfiniteGrp.powerImage (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) : ClosedSubgroup ↑G.toProfinite.toTop
```

**Native source docstring:** The closed range of the continuous pointwise power map.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L98) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.mem_powerImage_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.mem_powerImage_iff (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (x : ↑G.toProfinite.toTop) : x ∈ G.powerImage hG n ↔ ∃ (y : ↑G.toProfinite.toTop), y ^ n = x
```

**Native source docstring:** Membership in the closed power-image subgroup has an actual n-th-root
witness in the original group, not just a limit of powers.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L104) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_subgroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_subgroup (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) : ↑(G.powerImage hG n) = (G.powerHom hG n).range
```

**Native source docstring:** Forgetting closedness from `powerImage` gives the actual algebraic range
of `powerHom`; there is no additional closure operation in this projection.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L111) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_eq_topologicalClosure_zpowers

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_eq_topologicalClosure_zpowers (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℕ) : ↑(G.powerImage hG n) = (Subgroup.zpowers (g ^ n)).topologicalClosure
```

**Native source docstring:** Every topological generator gives a generator for the closed power image.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L116) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.topologicalClosure_zpowers_pow_eq

Kind: `theorem`.

```lean
theorem ProfiniteGrp.topologicalClosure_zpowers_pow_eq (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g k : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (hk : G.IsTopologicalGenerator k) (n : ℕ) : (Subgroup.zpowers (g ^ n)).topologicalClosure = (Subgroup.zpowers (k ^ n)).topologicalClosure
```

**Native source docstring:** The subgroup of n-th powers is independent of the chosen generator.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L145) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerHomToImage

Kind: `def`.

```lean
def ProfiniteGrp.powerHomToImage (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) : ↑G.toProfinite.toTop →ₜ* ↑(ofClosedSubgroup (G.powerImage hG n)).toProfinite.toTop
```

**Native source docstring:** The surjective continuous power map, now regarded as taking values in its
actual closed (and hence profinite) range.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L154) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerHomToImage_apply_coe

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerHomToImage_apply_coe (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (x : ↑G.toProfinite.toTop) : ↑((G.powerHomToImage hG n) x) = x ^ n
```

**Native source docstring:** Coercing the value of the surjective power map from its closed-subgroup
codomain back to `G` recovers the ordinary natural power.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L168) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerHomToImage_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerHomToImage_surjective (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) : Function.Surjective ⇑(G.powerHomToImage hG n)
```

**Native source docstring:** Every element of the power image has a preimage under the continuous
homomorphism into the closed-subgroup model.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L174) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerHomToImage_isTopologicalGenerator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerHomToImage_isTopologicalGenerator (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℕ) : (ofClosedSubgroup (G.powerImage hG n)).IsTopologicalGenerator ((G.powerHomToImage hG n) g)
```

**Native source docstring:** The n-th power of a topological generator is an actual topological
generator of the closed power image, viewed as a profinite group.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L182) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_isProcyclic

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_isProcyclic (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) : (ofClosedSubgroup (G.powerImage hG n)).IsProcyclic
```

**Native source docstring:** Every closed power image of a procyclic profinite group is procyclic,
including the zero-th power image.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L190) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_zero

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_zero (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) : ↑(G.powerImage hG 0) = ⊥
```

**Native source docstring:** The zero-th power image is the trivial subgroup; no openness is claimed.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L199) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_one

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_one (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) : ↑(G.powerImage hG 1) = ⊤
```

**Native source docstring:** Every element is a first power, so its image is the top subgroup.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L206) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_normal

Kind: `instance`.

```lean
instance ProfiniteGrp.powerImage_normal (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) : (↑(G.powerImage hG n)).Normal
```

**Native source docstring:** Every power image is normal, since the original group is commutative.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L213) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_quotient_zpowers_eq_top

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_quotient_zpowers_eq_top (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℕ) (hn : 0 < n) : Subgroup.zpowers ((QuotientGroup.mk' ↑(G.powerImage hG n)) g) = ⊤
```

**Native source docstring:** The quotient by a positive power image is generated by the image of any
supplied topological generator. In particular it is an abstract cyclic group.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L238) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_quotient_isCyclic

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_quotient_isCyclic (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℕ) (hn : 0 < n) : IsCyclic (↑G.toProfinite.toTop ⧸ ↑(G.powerImage hG n))
```

**Native source docstring:** The positive-power quotient is finite and cyclic.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L252) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_index_dvd

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_index_dvd (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (hn : 0 < n) : (↑(G.powerImage hG n)).index ∣ n
```

**Native source docstring:** For positive `n`, the index of the subgroup of n-th powers divides `n`.
There is no general equality: torsion can make the index smaller.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L260) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_finiteIndex

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_finiteIndex (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (hn : 0 < n) : (↑(G.powerImage hG n)).FiniteIndex
```

**Native source docstring:** Positive power images have finite index.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L280) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_quotient_finite

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_quotient_finite (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (hn : 0 < n) : Finite (↑G.toProfinite.toTop ⧸ ↑(G.powerImage hG n))
```

**Native source docstring:** The positive-power quotient is finite. Its cyclicity and the generating
class are given by `powerImage_quotient_isCyclic` and
`powerImage_quotient_zpowers_eq_top`.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L290) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerImage_isOpen

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerImage_isOpen (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (hn : 0 < n) : IsOpen ↑↑(G.powerImage hG n)
```

**Native source docstring:** Positive-power images are open subgroups of finite index.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L299) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerOpenSubgroup

Kind: `def`.

```lean
def ProfiniteGrp.powerOpenSubgroup (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (hn : 0 < n) : OpenSubgroup ↑G.toProfinite.toTop
```

**Native source docstring:** Package a positive power image as an open subgroup.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L307) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.powerOpenSubgroup_toSubgroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.powerOpenSubgroup_toSubgroup (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (hn : 0 < n) : ↑(G.powerOpenSubgroup hG n hn) = ↑(G.powerImage hG n)
```

**Native source docstring:** The open-subgroup packaging of a positive power image has exactly the
same underlying subgroup as the closed power image.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L312) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.openSubgroup_eq_powerImage

Kind: `theorem`.

```lean
theorem ProfiniteGrp.openSubgroup_eq_powerImage (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (H : OpenSubgroup ↑G.toProfinite.toTop) : ↑H = ↑(G.powerImage hG (↑H).index)
```

**Native source docstring:** Any open subgroup of a procyclic profinite group is precisely the image
of the power map at its actual index (with no extra normality assumption).

[Source](../ProfiniteGroups/ProcyclicPower.lean#L318) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.subgroup_eq_powerImage_of_isOpen

Kind: `theorem`.

```lean
theorem ProfiniteGrp.subgroup_eq_powerImage_of_isOpen (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (H : Subgroup ↑G.toProfinite.toTop) (hH : IsOpen ↑H) : H = ↑(G.powerImage hG H.index)
```

**Native source docstring:** The same classification for an ordinary subgroup accompanied by openness.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L353) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.openSubgroup_eq_of_index_eq

Kind: `theorem`.

```lean
theorem ProfiniteGrp.openSubgroup_eq_of_index_eq (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (H K : OpenSubgroup ↑G.toProfinite.toTop) (hindex : (↑H).index = (↑K).index) : H = K
```

**Native source docstring:** Open subgroups with equal index coincide.

[Source](../ProfiniteGroups/ProcyclicPower.lean#L359) (native source start line; generated entries may point to their parent).

#### Native instance table

- `ProfiniteGrp.powerImage_normal`: `Subgroup.Normal`; type names: `ClosedSubgroup.toSubgroup`

### ProfiniteGroups.ProcyclicQuotient

19 native named entries; 0 native instance-table rows.

#### ContinuousAddEquiv.toMultiplicative

Kind: `def`.

```lean
noncomputable def ContinuousAddEquiv.toMultiplicative {A : Type u} {B : Type v} [AddGroup A] [AddGroup B] [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ+ B) : Multiplicative A ≃ₜ* Multiplicative B
```

**Native source docstring:** An additive topological group equivalence is also an equivalence of the
corresponding multiplicatively written groups.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L27) (native source start line; generated entries may point to their parent).

#### Ideal.quotientContinuousAddEquivOfEq

Kind: `def`.

```lean
def Ideal.quotientContinuousAddEquivOfEq {R : Type u} [CommRing R] [TopologicalSpace R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃ₜ+ R ⧸ J
```

**Native source docstring:** Equality of ideals identifies their quotient topological additive groups.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L40) (native source start line; generated entries may point to their parent).

#### Ideal.quotientContinuousAddEquivOfEq_mk

Kind: `theorem`.

```lean
theorem Ideal.quotientContinuousAddEquivOfEq_mk {R : Type u} [CommRing R] [TopologicalSpace R] {I J : Ideal R} (h : I = J) (x : R) : (quotientContinuousAddEquivOfEq h) ((Quotient.mk I) x) = (Quotient.mk J) x
```

**Native source docstring:** Equality-of-ideals transport fixes quotient representatives.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L47) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicMapOfGenerator

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicMapOfGenerator (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : ↑primewisePadic.toProfinite.toTop →ₜ* ↑G.toProfinite.toTop
```

**Native source docstring:** The continuous primewise map determined by an element of a profinite
group.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L59) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicMapOfGenerator_diagonal

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicMapOfGenerator_diagonal (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (n : ℤ) : (G.primewisePadicMapOfGenerator g) (primewisePadicDiagonal n) = g ^ n
```

**Native source docstring:** The integral diagonal maps to the corresponding power of the supplied
element.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L67) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicMapOfGenerator_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicMapOfGenerator_surjective (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : Function.Surjective ⇑(G.primewisePadicMapOfGenerator g)
```

**Native source docstring:** A topological generator makes the primewise map surjective.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L75) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicAdditiveMap

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicAdditiveMap {Y : Type v} [Group Y] [TopologicalSpace Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : primewisePadicRing →+ Additive Y
```

**Native source docstring:** An additive homomorphism underlying a continuous map out of the
primewise product, with the target written additively.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L82) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdeal_toAddSubgroup

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdeal_toAddSubgroup {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) : Submodule.toAddSubgroup (primewisePadicKernelIdeal f) = (primewisePadicAdditiveMap f).ker
```

**Native source docstring:** The ideal attached to a map is exactly the additive kernel of its
underlying homomorphism.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L91) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdealAddEquiv

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicKernelIdealAddEquiv {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (hf : Function.Surjective ⇑f) : primewisePadicRing ⧸ primewisePadicKernelIdeal f ≃+ Additive Y
```

**Native source docstring:** The additive first isomorphism theorem, applied to the kernel ideal of
a surjective primewise map.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L102) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdealAddEquiv_mk

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdealAddEquiv_mk {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (hf : Function.Surjective ⇑f) (x : primewisePadicRing) : (primewisePadicKernelIdealAddEquiv f hf) ((Ideal.Quotient.mk (primewisePadicKernelIdeal f)) x) = Additive.ofMul (f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)))
```

**Native source docstring:** On a quotient representative, the additive equivalence agrees with the
original map.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L120) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdealContinuousMulEquiv

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicKernelIdealContinuousMulEquiv {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (hf : Function.Surjective ⇑f) : Multiplicative (primewisePadicRing ⧸ primewisePadicKernelIdeal f) ≃ₜ* Y
```

**Native source docstring:** A continuous surjection from the primewise p-adic group induces a
topological group equivalence from the multiplicative kernel-ideal quotient.
Compactness of the source and Hausdorffness of the target supply continuity
of the inverse.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L139) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdealContinuousMulEquiv_mk

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdealContinuousMulEquiv_mk {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (hf : Function.Surjective ⇑f) (x : primewisePadicRing) : (primewisePadicKernelIdealContinuousMulEquiv f hf) (Multiplicative.ofAdd ((Ideal.Quotient.mk (primewisePadicKernelIdeal f)) x)) = f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x))
```

**Native source docstring:** The kernel-ideal quotient sends a representative to its image.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L169) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdealContinuousMulEquiv_symm_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdealContinuousMulEquiv_symm_apply {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (hf : Function.Surjective ⇑f) (x : primewisePadicRing) : (primewisePadicKernelIdealContinuousMulEquiv f hf).symm (f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x))) = Multiplicative.ofAdd ((Ideal.Quotient.mk (primewisePadicKernelIdeal f)) x)
```

**Native source docstring:** The inverse equivalence takes the image of a representative back to its
kernel-ideal quotient class.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L182) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicContinuousMulEquivModel

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicContinuousMulEquivModel {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (hf : Function.Surjective ⇑f) : Y ≃ₜ* Multiplicative ↑(primewisePadicQuotientModel (primewisePadicKernelExponents f)).toProfinite.toTop
```

**Native source docstring:** A surjective primewise map identifies its target with the product
model of the exponent ideal of its kernel.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L196) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicContinuousMulEquivModel_apply_mk

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicContinuousMulEquivModel_apply_mk {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (hf : Function.Surjective ⇑f) (x : primewisePadicRing) (p : Nat.Primes) : Multiplicative.toAdd ((primewisePadicContinuousMulEquivModel f hf) (f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)))) p = (liftedPadicQuotientContinuousAddEquivFactor p (primewisePadicKernelExponents f p)) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p (primewisePadicKernelExponents f p))) (x p))
```

**Native source docstring:** Coordinate equation for a quotient representative under the inverse
target-to-product equivalence.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L209) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicExponentsOfGenerator

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicExponentsOfGenerator (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : Nat.Primes → ℕ∞
```

**Native source docstring:** The generator-dependent primewise kernel exponents.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L234) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.procyclicContinuousMulEquivModel

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.procyclicContinuousMulEquivModel (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : ↑G.toProfinite.toTop ≃ₜ* Multiplicative ↑(primewisePadicQuotientModel (G.primewisePadicExponentsOfGenerator g)).toProfinite.toTop
```

**Native source docstring:** A supplied topological generator gives an explicit product model, with
no assertion that the exponent family is generator-independent.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L239) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.procyclicContinuousMulEquivModel_zpow_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.procyclicContinuousMulEquivModel_zpow_apply (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℤ) (p : Nat.Primes) : Multiplicative.toAdd ((G.procyclicContinuousMulEquivModel g hg) (g ^ n)) p = (liftedPadicQuotientContinuousAddEquivFactor p (G.primewisePadicExponentsOfGenerator g p)) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p (G.primewisePadicExponentsOfGenerator g p))) (Multiplicative.toAdd (primewisePadicRingMultiplicativeEquiv.symm (primewisePadicDiagonal n)) p))
```

**Native source docstring:** The generator's powers have the expected product-model coordinates.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L249) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.procyclicContinuousMulEquivModel_zsmul_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.procyclicContinuousMulEquivModel_zsmul_apply (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℤ) (p : Nat.Primes) : (n • Multiplicative.toAdd ((G.procyclicContinuousMulEquivModel g hg) g)) p = (liftedPadicQuotientContinuousAddEquivFactor p (G.primewisePadicExponentsOfGenerator g p)) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p (G.primewisePadicExponentsOfGenerator g p))) (Multiplicative.toAdd (primewisePadicRingMultiplicativeEquiv.symm (primewisePadicDiagonal n)) p))
```

**Native source docstring:** Simp-normal coordinates of an integral multiple of the model generator.
The power-coordinate theorem remains available by name; this form also applies
after `map_zpow` and `toAdd_zpow` normalize its left-hand side.

[Source](../ProfiniteGroups/ProcyclicQuotient.lean#L263) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.ProcyclicRealization

21 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.instFactPrimeValNat_profiniteGroups_4

Kind: `theorem`.

```lean
theorem ProfiniteGrp.instFactPrimeValNat_profiniteGroups_4 (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L27) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicProcyclicModel

Kind: `def`.

```lean
noncomputable abbrev ProfiniteGrp.primewisePadicProcyclicModel (e : Nat.Primes → ℕ∞) : ProfiniteGrp.{u}
```

**Native source docstring:** The multiplicative presentation of the existing additive product model.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L29) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationMap

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicRealizationMap (e : Nat.Primes → ℕ∞) : ↑primewisePadic.toProfinite.toTop →ₜ* ↑(primewisePadicProcyclicModel e).toProfinite.toTop
```

**Native source docstring:** The continuous projection onto the quotient by a primewise exponent ideal,
followed by the existing quotient-to-product equivalence.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L34) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationMap_apply

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationMap_apply (e : Nat.Primes → ℕ∞) (x : primewisePadicRing) : (primewisePadicRealizationMap e) (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) = Multiplicative.ofAdd ((primewisePadicQuotientContinuousAddEquivModel e) ((Ideal.Quotient.mk (primewisePadicIdealOfExponents e)) x))
```

**Native source docstring:** The canonical map sends a ring representative to its quotient class in the
mixed product model.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L45) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationMap_apply_coordinate

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationMap_apply_coordinate (e : Nat.Primes → ℕ∞) (x : primewisePadicRing) (p : Nat.Primes) : Multiplicative.toAdd ((primewisePadicRealizationMap e) (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x))) p = (liftedPadicQuotientContinuousAddEquivFactor p (e p)) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p (e p))) (x p))
```

**Native source docstring:** Each coordinate of the canonical map comes from its original factor quotient.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L57) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationMap_diagonal_coordinate

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationMap_diagonal_coordinate (e : Nat.Primes → ℕ∞) (n : ℤ) (p : Nat.Primes) : Multiplicative.toAdd ((primewisePadicRealizationMap e) (primewisePadicDiagonal n)) p = (liftedPadicQuotientContinuousAddEquivFactor p (e p)) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p (e p))) { down := ↑n })
```

**Native source docstring:** Integral inputs produce their own residue or p-adic coordinate class.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L68) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationMap_diagonal_top_coordinate

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationMap_diagonal_top_coordinate (e : Nat.Primes → ℕ∞) (n : ℤ) (p : Nat.Primes) (hp : e p = ⊤) : Multiplicative.toAdd ((primewisePadicRealizationMap e) (primewisePadicDiagonal n)) p ≍ { down := ↑n }
```

**Native source docstring:** At an infinite exponent, the image of an integer is its p-adic cast.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L81) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationMap_diagonal_natCast_coordinate

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationMap_diagonal_natCast_coordinate (e : Nat.Primes → ℕ∞) (n : ℤ) (p : Nat.Primes) (k : ℕ) (hp : e p = ↑k) : Multiplicative.toAdd ((primewisePadicRealizationMap e) (primewisePadicDiagonal n)) p ≍ { down := (PadicInt.toZModPow k) ↑n }
```

**Native source docstring:** At a finite exponent, the image of an integer is reduced modulo `p ^ k`.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L96) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationMap_surjective

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationMap_surjective (e : Nat.Primes → ℕ∞) : Function.Surjective ⇑(primewisePadicRealizationMap e)
```

**Native source docstring:** The canonical map is onto for all exponent families.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L113) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelIdeal_realizationMap

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelIdeal_realizationMap (e : Nat.Primes → ℕ∞) : primewisePadicKernelIdeal (primewisePadicRealizationMap e) = primewisePadicIdealOfExponents e
```

**Native source docstring:** The *actual* kernel of the canonical map is the chosen product ideal.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L122) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicKernelExponents_realizationMap

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicKernelExponents_realizationMap (e : Nat.Primes → ℕ∞) : primewisePadicKernelExponents (primewisePadicRealizationMap e) = e
```

**Native source docstring:** Exponents extracted from the computed kernel are precisely the input.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L140) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationGenerator

Kind: `def`.

```lean
noncomputable def ProfiniteGrp.primewisePadicRealizationGenerator (e : Nat.Primes → ℕ∞) : ↑(primewisePadicProcyclicModel e).toProfinite.toTop
```

**Native source docstring:** The image of the additive integral diagonal in the product model.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L147) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationGenerator_coordinate

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationGenerator_coordinate (e : Nat.Primes → ℕ∞) (p : Nat.Primes) : Multiplicative.toAdd (primewisePadicRealizationGenerator e) p = (liftedPadicQuotientContinuousAddEquivFactor p (e p)) ((Ideal.Quotient.mk (liftedPadicIdealOfExponent p (e p))) { down := 1 })
```

**Native source docstring:** The generator is defined as the image of the additive *one* diagonal;
the multiplicative identity is the image of the additive zero diagonal.
These images can coincide after quotienting, in particular when all exponents are zero.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L152) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationMap_diagonal_zero

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationMap_diagonal_zero (e : Nat.Primes → ℕ∞) : (primewisePadicRealizationMap e) (primewisePadicDiagonal 0) = 1
```

**Native source docstring:** The multiplicative identity is the image of additive zero.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L164) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationMap_diagonal

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationMap_diagonal (e : Nat.Primes → ℕ∞) (n : ℤ) : (primewisePadicRealizationMap e) (primewisePadicDiagonal n) = primewisePadicRealizationGenerator e ^ n
```

**Native source docstring:** The image of an integral diagonal element is the corresponding integral
power of the realized generator, including the trivial all-zero quotient.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L174) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicRealizationGenerator_isTopologicalGenerator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicRealizationGenerator_isTopologicalGenerator (e : Nat.Primes → ℕ∞) : (primewisePadicProcyclicModel e).IsTopologicalGenerator (primewisePadicRealizationGenerator e)
```

**Native source docstring:** The explicit image of the diagonal generates the entire product model.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L186) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicProcyclicModel_isProcyclic

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicProcyclicModel_isProcyclic (e : Nat.Primes → ℕ∞) : (primewisePadicProcyclicModel e).IsProcyclic
```

**Native source docstring:** The model is genuinely procyclic, including all finite, top, zero and mixed families.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L194) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicMapOfRealizationGenerator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicMapOfRealizationGenerator (e : Nat.Primes → ℕ∞) : (primewisePadicProcyclicModel e).primewisePadicMapOfGenerator (primewisePadicRealizationGenerator e) = primewisePadicRealizationMap e
```

**Native source docstring:** The generator-induced map agrees with the quotient map, since both agree
on the dense integral diagonal.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L200) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicProcyclicModel_exponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicProcyclicModel_exponents (e : Nat.Primes → ℕ∞) (h : (primewisePadicProcyclicModel e).IsProcyclic) : h.exponents = e
```

**Native source docstring:** Every procyclicity proof of the model has the prescribed invariant.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L219) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.exists_procyclic_of_exponents

Kind: `theorem`.

```lean
theorem ProfiniteGrp.exists_procyclic_of_exponents (e : Nat.Primes → ℕ∞) : ∃ (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic), hG.exponents = e
```

**Native source docstring:** Every primewise exponent family is realized in any requested universe.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L231) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicProcyclicModel_nonempty_equiv_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicProcyclicModel_nonempty_equiv_iff (e f : Nat.Primes → ℕ∞) : Nonempty (↑(primewisePadicProcyclicModel e).toProfinite.toTop ≃ₜ* ↑(primewisePadicProcyclicModel f).toProfinite.toTop) ↔ e = f
```

**Native source docstring:** Models in independent universes are continuously equivalent exactly
when their primewise exponents agree.

[Source](../ProfiniteGroups/ProcyclicRealization.lean#L238) (native source start line; generated entries may point to their parent).

### ProfiniteGroups.ProcyclicTorsionFree

5 native named entries; 0 native instance-table rows.

#### ProfiniteGrp.instFactPrimeValNat_profiniteGroups_4

Kind: `theorem`.

```lean
theorem ProfiniteGrp.instFactPrimeValNat_profiniteGroups_4 (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../ProfiniteGroups/ProcyclicTorsionFree.lean#L31) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.padicQuotientFactor_isAddTorsionFree_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.padicQuotientFactor_isAddTorsionFree_iff (p : Nat.Primes) (e : ℕ∞) : IsAddTorsionFree ↑(padicQuotientFactor p e).toProfinite.toTop ↔ e = 0 ∨ e = ⊤
```

**Native source docstring:** A p-adic quotient factor is additively torsion-free exactly for zero or
infinite exponent. The exponent-zero factor is the trivial group `ZMod 1`.

[Source](../ProfiniteGroups/ProcyclicTorsionFree.lean#L68) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicQuotientModel_isAddTorsionFree_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicQuotientModel_isAddTorsionFree_iff (e : Nat.Primes → ℕ∞) : IsAddTorsionFree ↑(primewisePadicQuotientModel e).toProfinite.toTop ↔ ∀ (p : Nat.Primes), e p = 0 ∨ e p = ⊤
```

**Native source docstring:** The complete primewise quotient model is torsion-free precisely when every
coordinate is trivial or an entire p-adic integer factor.

[Source](../ProfiniteGroups/ProcyclicTorsionFree.lean#L86) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.primewisePadicSurjective_isMulTorsionFree_iff

Kind: `theorem`.

```lean
theorem ProfiniteGrp.primewisePadicSurjective_isMulTorsionFree_iff {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y] (f : ↑primewisePadic.toProfinite.toTop →ₜ* Y) (hf : Function.Surjective ⇑f) : IsMulTorsionFree Y ↔ ∀ (p : Nat.Primes), primewisePadicKernelExponents f p = 0 ∨ primewisePadicKernelExponents f p = ⊤
```

**Native source docstring:** A surjective continuous image of the primewise p-adic group is torsion-free
exactly when every exponent of its kernel quotient is zero or infinite. The
target need not be assumed commutative.

[Source](../ProfiniteGroups/ProcyclicTorsionFree.lean#L114) (native source start line; generated entries may point to their parent).

#### ProfiniteGrp.isMulTorsionFree_iff_exponentsOfGenerator

Kind: `theorem`.

```lean
theorem ProfiniteGrp.isMulTorsionFree_iff_exponentsOfGenerator (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : IsMulTorsionFree ↑G.toProfinite.toTop ↔ ∀ (p : Nat.Primes), G.primewisePadicExponentsOfGenerator g p = 0 ∨ G.primewisePadicExponentsOfGenerator g p = ⊤
```

**Native source docstring:** A profinite group with a supplied topological generator is torsion-free
exactly when its generator-dependent primewise quotient exponents are zero or
infinite.

[Source](../ProfiniteGroups/ProcyclicTorsionFree.lean#L148) (native source start line; generated entries may point to their parent).

## Checked-use clients

### ProfiniteGroupsTests

0 native named entries; 0 native instance-table rows.

No new named declarations in this module.

### Tests.DirectImports

6 native named entries; 0 native instance-table rows.

#### DirectImportsTests.zeroOnePowerImages

Kind: `theorem`.

```lean
theorem DirectImportsTests.zeroOnePowerImages (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) : ↑(G.powerImage hG 0) = ⊥ ∧ ↑(G.powerImage hG 1) = ⊤
```

**Native source docstring:** Power zero gives the bottom subgroup; power one gives the whole group.

[Source](../Tests/DirectImports.lean#L26) (native source start line; generated entries may point to their parent).

#### DirectImportsTests.positivePowerQuotient

Kind: `theorem`.

```lean
theorem DirectImportsTests.positivePowerQuotient (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℕ) (hn : 0 < n) : IsOpen ↑↑(G.powerImage hG n) ∧ IsCyclic (↑G.toProfinite.toTop ⧸ ↑(G.powerImage hG n)) ∧ Finite (↑G.toProfinite.toTop ⧸ ↑(G.powerImage hG n)) ∧ (↑(G.powerImage hG n)).index ∣ n
```

**Native source docstring:** A positive exponent gives a finite cyclic quotient and an open image.

[Source](../Tests/DirectImports.lean#L32) (native source start line; generated entries may point to their parent).

#### DirectImportsTests.cyclicTwelvePositivePower

Kind: `theorem`.

```lean
theorem DirectImportsTests.cyclicTwelvePositivePower : IsOpen ↑↑((ProfiniteGrp.finiteCyclic 12).powerImage ⋯ 4) ∧ (↑((ProfiniteGrp.finiteCyclic 12).powerImage ⋯ 4)).index ∣ 4
```

**Native source docstring:** The fourth-power image in the finite cyclic group of order twelve is open.

[Source](../Tests/DirectImports.lean#L44) (native source start line; generated entries may point to their parent).

#### DirectImportsTests.mixedProfile

Kind: `def`.

```lean
def DirectImportsTests.mixedProfile (p : Nat.Primes) : ℕ∞
```

**Native source docstring:** A profile for the actual ideal-kernel check, with all three exponent regimes.

[Source](../Tests/DirectImports.lean#L52) (native source start line; generated entries may point to their parent).

#### DirectImportsTests.actualMixedKernel

Kind: `theorem`.

```lean
theorem DirectImportsTests.actualMixedKernel : ProfiniteGrp.primewisePadicKernelIdeal (ProfiniteGrp.primewisePadicRealizationMap mixedProfile) = ProfiniteGrp.primewisePadicIdealOfExponents mixedProfile
```

**Native source docstring:** The realization map's actual ideal kernel is the prescribed mixed ideal.

[Source](../Tests/DirectImports.lean#L56) (native source start line; generated entries may point to their parent).

#### DirectImportsTests.zeroTopExtracted

Kind: `theorem`.

```lean
theorem DirectImportsTests.zeroTopExtracted : (ProfiniteGrp.primewisePadicKernelExponents (ProfiniteGrp.primewisePadicRealizationMap fun (x : Nat.Primes) => 0) = fun (x : Nat.Primes) => 0) ∧ ProfiniteGrp.primewisePadicKernelExponents (ProfiniteGrp.primewisePadicRealizationMap fun (x : Nat.Primes) => ⊤) = fun (x : Nat.Primes) => ⊤
```

**Native source docstring:** Both extreme profiles are recovered using only the realization leaf.

[Source](../Tests/DirectImports.lean#L63) (native source start line; generated entries may point to their parent).

### Tests.PrimewisePadicIdealTransport

1 native named entries; 0 native instance-table rows.

#### instFactPrimeValNat_tests

Kind: `theorem`.

```lean
theorem instFactPrimeValNat_tests (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../Tests/PrimewisePadicIdealTransport.lean#L23) (native source start line; generated entries may point to their parent).

### Tests.PrimewisePadicKernelTransport

26 native named entries; 0 native instance-table rows.

#### PrimewisePadicKernelTransportTests.commutingSquare

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.commutingSquare (x : ProfiniteGrp.primewisePadicRing) : ProfiniteGrp.primewisePadicChangeUniverse (ProfiniteGrp.primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) = ProfiniteGrp.primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd (ProfiniteGrp.primewisePadicRingChangeUniverse x))
```

**Original catalogue explanation (not a Lean docstring):** Checks that universe transport commutes with additive-to-multiplicative comparison.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L24) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.arbitraryMapKernelMembership

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.arbitraryMapKernelMembership {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop →ₜ* Y) (x : ProfiniteGrp.primewisePadicRing) : x ∈ ProfiniteGrp.primewisePadicKernelIdeal (f.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) ↔ f (ProfiniteGrp.primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd (ProfiniteGrp.primewisePadicRingChangeUniverse x))) = 1
```

**Original catalogue explanation (not a Lean docstring):** Membership in the transported kernel ideal is tested by evaluating the map after the corresponding ring universe change.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L31) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.arbitraryMapIdeal

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.arbitraryMapIdeal {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop →ₜ* Y) : ProfiniteGrp.primewisePadicKernelIdeal (f.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) = Ideal.comap ProfiniteGrp.primewisePadicRingChangeUniverse (ProfiniteGrp.primewisePadicKernelIdeal f)
```

**Original catalogue explanation (not a Lean docstring):** Pullback of the kernel ideal along a universe change matches the ideal of the composite map.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L42) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.arbitraryMapExponents

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.arbitraryMapExponents {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop →ₜ* Y) : ProfiniteGrp.primewisePadicKernelExponents (f.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) = ProfiniteGrp.primewisePadicKernelExponents f
```

**Original catalogue explanation (not a Lean docstring):** Kernel exponents of an arbitrary target map are unchanged by primewise universe transport.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L51) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.zeroToPositive

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.zeroToPositive {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop →ₜ* Y) : ProfiniteGrp.primewisePadicKernelExponents (f.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) = ProfiniteGrp.primewisePadicKernelExponents f
```

**Original catalogue explanation (not a Lean docstring):** Tests preservation of exponents while transporting a map from universe zero to universe one.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L60) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.positiveToZero

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.positiveToZero {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y] (f : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop →ₜ* Y) : ProfiniteGrp.primewisePadicKernelIdeal (f.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) = Ideal.comap ProfiniteGrp.primewisePadicRingChangeUniverse (ProfiniteGrp.primewisePadicKernelIdeal f)
```

**Original catalogue explanation (not a Lean docstring):** Tests pullback of kernel ideals when transporting from universe one to zero.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L69) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.identityInfinite

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.identityInfinite (p : Nat.Primes) : ProfiniteGrp.primewisePadicKernelExponents ((ContinuousMonoidHom.id ↑ProfiniteGrp.primewisePadic.toProfinite.toTop).comp ↑ProfiniteGrp.primewisePadicChangeUniverse) p = ⊤
```

**Original catalogue explanation (not a Lean docstring):** The identity map after universe transport has infinite exponent at each prime.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L78) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.trivialZero

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.trivialZero (p : Nat.Primes) : ProfiniteGrp.primewisePadicKernelExponents (ContinuousMonoidHom.comp 1 ↑ProfiniteGrp.primewisePadicChangeUniverse) p = 0
```

**Original catalogue explanation (not a Lean docstring):** The trivial map after universe transport has zero exponent at each prime.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L88) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.arbitraryElementComparison

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.arbitraryElementComparison (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) : ProfiniteGrp.primewisePadicKernelExponents (G.primewisePadicBaseMapOfGenerator g) = G.primewisePadicExponentsOfGenerator g
```

**Original catalogue explanation (not a Lean docstring):** Compares the generator-based exponent family with the actual kernel exponent family without requiring the element to generate.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L96) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.nongeneratorConstant

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.nongeneratorConstant (x : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop) : ((ProfiniteGrp.finiteCyclic 12).primewisePadicBaseMapOfGenerator 1) x = 1
```

**Original catalogue explanation (not a Lean docstring):** The base map selected by the identity element of the cyclic group of order twelve is constant.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L101) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.nongeneratorZero

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.nongeneratorZero (p : Nat.Primes) : (ProfiniteGrp.finiteCyclic 12).primewisePadicExponentsOfGenerator 1 p = 0
```

**Original catalogue explanation (not a Lean docstring):** The identity element's primewise exponent family in that cyclic group is zero.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L110) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.nongeneratorNotSurjective

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.nongeneratorNotSurjective : ¬Function.Surjective ⇑((ProfiniteGrp.finiteCyclic 12).primewisePadicBaseMapOfGenerator 1)
```

**Original catalogue explanation (not a Lean docstring):** The base map of that nongenerator cannot surject onto the nontrivial cyclic group.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L117) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.twoPrime

Kind: `def`.

```lean
def PrimewisePadicKernelTransportTests.twoPrime : Nat.Primes
```

**Native source docstring:** The prime two, used for concrete transport checks.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L126) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.threePrime

Kind: `def`.

```lean
def PrimewisePadicKernelTransportTests.threePrime : Nat.Primes
```

**Native source docstring:** The prime three, used for concrete transport checks.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L128) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.fivePrime

Kind: `def`.

```lean
def PrimewisePadicKernelTransportTests.fivePrime : Nat.Primes
```

**Native source docstring:** The prime five, used for concrete transport checks.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L130) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedExponents

Kind: `def`.

```lean
noncomputable def PrimewisePadicKernelTransportTests.mixedExponents (p : Nat.Primes) : ℕ∞
```

**Native source docstring:** The zero/finite/infinite profile for kernel universe transport.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L133) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedMap

Kind: `def`.

```lean
noncomputable def PrimewisePadicKernelTransportTests.mixedMap : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop →ₜ* Multiplicative ↑(ProfiniteGrp.primewisePadicQuotientModel mixedExponents).toProfinite.toTop
```

**Native source docstring:** The realization map used to check the actual transported kernel.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L137) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedMap_mk

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.mixedMap_mk (x : ProfiniteGrp.primewisePadicRing) : mixedMap (ProfiniteGrp.primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) = Multiplicative.ofAdd ((ProfiniteGrp.primewisePadicQuotientContinuousAddEquivModel mixedExponents) ((Ideal.Quotient.mk (ProfiniteGrp.primewisePadicIdealOfExponents mixedExponents)) x))
```

**Original catalogue explanation (not a Lean docstring):** Checks the evaluation of the mixed-profile map on a represented element.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L158) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedMap_kernelIdeal

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.mixedMap_kernelIdeal : ProfiniteGrp.primewisePadicKernelIdeal mixedMap = ProfiniteGrp.primewisePadicIdealOfExponents mixedExponents
```

**Original catalogue explanation (not a Lean docstring):** Checks the kernel ideal computed for the mixed finite/infinite/zero profile map.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L165) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedKernelIdeal

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.mixedKernelIdeal : ProfiniteGrp.primewisePadicKernelIdeal (mixedMap.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) = ProfiniteGrp.primewisePadicIdealOfExponents mixedExponents
```

**Original catalogue explanation (not a Lean docstring):** Checks the mixed-profile kernel ideal against its coordinate description.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L182) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedExponent

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.mixedExponent (p : Nat.Primes) : ProfiniteGrp.primewisePadicKernelExponents (mixedMap.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) p = mixedExponents p
```

**Original catalogue explanation (not a Lean docstring):** Reads off the mixed map's primewise exponent family.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L190) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedZero

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.mixedZero : ProfiniteGrp.primewisePadicKernelExponents (mixedMap.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) twoPrime = 0
```

**Original catalogue explanation (not a Lean docstring):** Tests the zero-exponent coordinate of the mixed map.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L198) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedFinite

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.mixedFinite : ProfiniteGrp.primewisePadicKernelExponents (mixedMap.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) threePrime = 2
```

**Original catalogue explanation (not a Lean docstring):** Tests the finite positive-exponent coordinate of the mixed map.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L205) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedInfinite

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.mixedInfinite : ProfiniteGrp.primewisePadicKernelExponents (mixedMap.comp ↑ProfiniteGrp.primewisePadicChangeUniverse) fivePrime = ⊤
```

**Original catalogue explanation (not a Lean docstring):** Tests the infinite-exponent coordinate of the mixed map.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L212) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedNotTrivial

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.mixedNotTrivial : mixedMap.comp ↑ProfiniteGrp.primewisePadicChangeUniverse ≠ 1
```

**Original catalogue explanation (not a Lean docstring):** The mixed-profile map is not the constant homomorphism.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L219) (native source start line; generated entries may point to their parent).

#### PrimewisePadicKernelTransportTests.mixedNotInjective

Kind: `theorem`.

```lean
theorem PrimewisePadicKernelTransportTests.mixedNotInjective : ¬Function.Injective ⇑(mixedMap.comp ↑ProfiniteGrp.primewisePadicChangeUniverse)
```

**Original catalogue explanation (not a Lean docstring):** A positive finite exponent yields a nontrivial kernel for the mixed map.

[Source](../Tests/PrimewisePadicKernelTransport.lean#L227) (native source start line; generated entries may point to their parent).

### Tests.PrimewisePadicQuotients

2 native named entries; 0 native instance-table rows.

#### instFactPrimeValNat_tests

Kind: `theorem`.

```lean
theorem instFactPrimeValNat_tests (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../Tests/PrimewisePadicQuotients.lean#L57) (native source start line; generated entries may point to their parent).

#### mixedExponents

Kind: `def`.

```lean
noncomputable def mixedExponents (q : Nat.Primes) : ℕ∞
```

**Native source docstring:** A shared quotient profile: zero at two, finite at three, top otherwise.

[Source](../Tests/PrimewisePadicQuotients.lean#L90) (native source start line; generated entries may point to their parent).

### Tests.ProcyclicBaseMap

5 native named entries; 0 native instance-table rows.

#### ProcyclicBaseMapTests.transCoordinates

Kind: `theorem`.

```lean
theorem ProcyclicBaseMapTests.transCoordinates (x : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop) (p : Nat.Primes) : (Multiplicative.toAdd ((ProfiniteGrp.primewisePadicChangeUniverse.trans ProfiniteGrp.primewisePadicChangeUniverse) x p)).down = (Multiplicative.toAdd (x p)).down
```

**Native source docstring:** The composition law preserves coordinates in three independent universes.

[Source](../Tests/ProcyclicBaseMap.lean#L26) (native source start line; generated entries may point to their parent).

#### ProcyclicBaseMapTests.finite12Surjective

Kind: `theorem`.

```lean
theorem ProcyclicBaseMapTests.finite12Surjective : Function.Surjective ⇑((ProfiniteGrp.finiteCyclic 12).primewisePadicBaseMapOfGenerator (ProfiniteGrp.finiteCyclicGenerator 12))
```

**Native source docstring:** The finite cyclic group of order twelve has a common-source surjection.

[Source](../Tests/ProcyclicBaseMap.lean#L86) (native source start line; generated entries may point to their parent).

#### ProcyclicBaseMapTests.equivNaturality

Kind: `theorem`.

```lean
theorem ProcyclicBaseMapTests.equivNaturality (g : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop) : (↑ProfiniteGrp.primewisePadicChangeUniverse).comp (ProfiniteGrp.primewisePadic.primewisePadicBaseMapOfGenerator g) = ProfiniteGrp.primewisePadic.primewisePadicBaseMapOfGenerator (ProfiniteGrp.primewisePadicChangeUniverse g)
```

**Native source docstring:** Naturality for a continuous equivalence between independent universes.

[Source](../Tests/ProcyclicBaseMap.lean#L98) (native source start line; generated entries may point to their parent).

#### ProcyclicBaseMapTests.finite12ConstantNotSurjective

Kind: `theorem`.

```lean
theorem ProcyclicBaseMapTests.finite12ConstantNotSurjective : ¬Function.Surjective ⇑1
```

**Native source docstring:** The finite endomorphism used for naturality is not surjective.

[Source](../Tests/ProcyclicBaseMap.lean#L115) (native source start line; generated entries may point to their parent).

#### ProcyclicBaseMapTests.finite12OneNotGenerator

Kind: `theorem`.

```lean
theorem ProcyclicBaseMapTests.finite12OneNotGenerator : ¬(ProfiniteGrp.finiteCyclic 12).IsTopologicalGenerator 1
```

**Native source docstring:** The identity in the nontrivial finite cyclic group is not a generator.

[Source](../Tests/ProcyclicBaseMap.lean#L135) (native source start line; generated entries may point to their parent).

### Tests.ProcyclicGeneratorIndependence

1 native named entries; 0 native instance-table rows.

#### instFactPrimeValNat_tests_1

Kind: `theorem`.

```lean
theorem instFactPrimeValNat_tests_1 (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../Tests/ProcyclicGeneratorIndependence.lean#L24) (native source start line; generated entries may point to their parent).

### Tests.ProcyclicHom

26 native named entries; 0 native instance-table rows.

#### ProcyclicHomTests.arbitraryTarget

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.arbitraryTarget (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) : (∃! f : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop, f g = h) ↔ ∀ (p : Nat.Primes), ProfiniteGrp.primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p
```

**Original catalogue explanation (not a Lean docstring):** Evaluation at a chosen generator characterizes maps even when the target is not procyclic.

[Source](../Tests/ProcyclicHom.lean#L25) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.evaluationDeterminesMap

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.evaluationDeterminesMap (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (f k : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop) (heq : f g = k g) : f = k
```

**Original catalogue explanation (not a Lean docstring):** Two maps with the same value on a supplied generator agree.

[Source](../Tests/ProcyclicHom.lean#L32) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.factorCommutes

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.factorCommutes (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) (ha : ∀ (p : Nat.Primes), ProfiniteGrp.primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p) : (ProfiniteGrp.factorOfGenerator hG g hg h ha).comp (G.primewisePadicBaseMapOfGenerator g) = H.primewisePadicBaseMapOfGenerator h ∧ (ProfiniteGrp.factorOfGenerator hG g hg h ha) g = h
```

**Original catalogue explanation (not a Lean docstring):** The factorization of a homomorphism through its exponent profile preserves the original map.

[Source](../Tests/ProcyclicHom.lean#L37) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.surjectionTest

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.surjectionTest (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) (ha : ∀ (p : Nat.Primes), ProfiniteGrp.primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p) : Function.Surjective ⇑(ProfiniteGrp.factorOfGenerator hG g hg h ha) ↔ H.IsTopologicalGenerator h
```

**Original catalogue explanation (not a Lean docstring):** Under the prescribed-image admissibility condition, the factor map is surjective exactly when that image generates the target.

[Source](../Tests/ProcyclicHom.lean#L47) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.quotientOrder

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.quotientOrder (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (hG : G.IsProcyclic) (hH : H.IsProcyclic) : (∃ (f : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop), Function.Surjective ⇑f) ↔ ∀ (p : Nat.Primes), hH.exponents p ≤ hG.exponents p
```

**Original catalogue explanation (not a Lean docstring):** A continuous surjection between procyclic profinite groups exists exactly when every target exponent is at most the corresponding source exponent.

[Source](../Tests/ProcyclicHom.lean#L54) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.positiveIndependentUniverses

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.positiveIndependentUniverses (G : ProfiniteGrp.{1}) (H : ProfiniteGrp.{2}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) (ha : ∀ (p : Nat.Primes), ProfiniteGrp.primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p) : (ProfiniteGrp.factorOfGenerator hG g hg h ha).comp (G.primewisePadicBaseMapOfGenerator g) = H.primewisePadicBaseMapOfGenerator h
```

**Original catalogue explanation (not a Lean docstring):** Checks the factor/base-map commuting equation for source and target in independent positive universes.

[Source](../Tests/ProcyclicHom.lean#L59) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.fourProfile

Kind: `def`.

```lean
def ProcyclicHomTests.fourProfile (p : Nat.Primes) : ℕ∞
```

**Native source docstring:** A four-element profile supported at two.

[Source](../Tests/ProcyclicHom.lean#L67) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.twoProfile

Kind: `def`.

```lean
def ProcyclicHomTests.twoProfile (p : Nat.Primes) : ℕ∞
```

**Native source docstring:** A two-element profile supported at two.

[Source](../Tests/ProcyclicHom.lean#L69) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.finiteProfileQuotient

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.finiteProfileQuotient : ∃ (f : ↑(ProfiniteGrp.primewisePadicProcyclicModel fourProfile).toProfinite.toTop →ₜ* ↑(ProfiniteGrp.primewisePadicProcyclicModel twoProfile).toProfinite.toTop), Function.Surjective ⇑f
```

**Original catalogue explanation (not a Lean docstring):** Tests the positive finite cyclic quotient profile.

[Source](../Tests/ProcyclicHom.lean#L72) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.finiteProfileReverseImpossible

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.finiteProfileReverseImpossible : ¬∃ (f : ↑(ProfiniteGrp.primewisePadicProcyclicModel twoProfile).toProfinite.toTop →ₜ* ↑(ProfiniteGrp.primewisePadicProcyclicModel fourProfile).toProfinite.toTop), Function.Surjective ⇑f
```

**Original catalogue explanation (not a Lean docstring):** There is no continuous surjection from the order-two model onto the order-four model.

[Source](../Tests/ProcyclicHom.lean#L83) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.targetIdentityAlways

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.targetIdentityAlways (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : ProfiniteGrp.factorOfGenerator hG g hg 1 ⋯ = 1
```

**Original catalogue explanation (not a Lean docstring):** The identity of any target group is an admissible image of a generator.

[Source](../Tests/ProcyclicHom.lean#L93) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.identityNeverSurjectsOntoCyclicTwo

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.identityNeverSurjectsOntoCyclicTwo (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : ¬Function.Surjective ⇑(ProfiniteGrp.factorOfGenerator hG g hg 1 ⋯)
```

**Original catalogue explanation (not a Lean docstring):** Sending a generator to the identity cannot surject onto the nontrivial cyclic group of order two.

[Source](../Tests/ProcyclicHom.lean#L98) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.klein

Kind: `def`.

```lean
def ProcyclicHomTests.klein : ProfiniteGrp.{0}
```

**Native source docstring:** The finite Klein four-group, used as a potentially nonprocyclic target.

[Source](../Tests/ProcyclicHom.lean#L110) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.kleinNotProcyclic

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.kleinNotProcyclic : ¬klein.IsProcyclic
```

**Original catalogue explanation (not a Lean docstring):** The Klein four group provides a finite target that is not procyclic.

[Source](../Tests/ProcyclicHom.lean#L114) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.mapIntoFiniteNoncyclicTarget

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.mapIntoFiniteNoncyclicTarget : ∃! f : ↑(ProfiniteGrp.finiteCyclic 4).toProfinite.toTop →ₜ* ↑klein.toProfinite.toTop, f (ProfiniteGrp.finiteCyclicGenerator 4) = 1
```

**Original catalogue explanation (not a Lean docstring):** Tests the generator-image criterion for a map into a nonprocyclic finite target.

[Source](../Tests/ProcyclicHom.lean#L171) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.squareHom

Kind: `def`.

```lean
def ProcyclicHomTests.squareHom : ↑(ProfiniteGrp.finiteCyclic 4).toProfinite.toTop →ₜ* ↑(ProfiniteGrp.finiteCyclic 4).toProfinite.toTop
```

**Native source docstring:** The endomorphism of the cyclic group of order four given by squaring.

[Source](../Tests/ProcyclicHom.lean#L180) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.squareNotSurjective

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.squareNotSurjective : ¬Function.Surjective ⇑squareHom
```

**Original catalogue explanation (not a Lean docstring):** The squaring endomorphism on the selected finite cyclic group is not surjective.

[Source](../Tests/ProcyclicHom.lean#L190) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.squareAdmissible

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.squareAdmissible (p : Nat.Primes) : ProfiniteGrp.primewisePadicKernelExponents ((ProfiniteGrp.finiteCyclic 4).primewisePadicBaseMapOfGenerator (squareHom (ProfiniteGrp.finiteCyclicGenerator 4))) p ≤ ⋯.exponents p
```

**Original catalogue explanation (not a Lean docstring):** Squaring still defines a valid continuous homomorphism without being onto.

[Source](../Tests/ProcyclicHom.lean#L207) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.squareImageNotOnto

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.squareImageNotOnto : ¬Function.Surjective ⇑(ProfiniteGrp.factorOfGenerator ⋯ (ProfiniteGrp.finiteCyclicGenerator 4) ⋯ (squareHom (ProfiniteGrp.finiteCyclicGenerator 4)) squareAdmissible)
```

**Original catalogue explanation (not a Lean docstring):** The image of the squaring map is a proper subgroup in this example.

[Source](../Tests/ProcyclicHom.lean#L221) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.zeroSourceToZeroTarget

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.zeroSourceToZeroTarget : ∃! f : ↑(ProfiniteGrp.primewisePadicProcyclicModel fun (x : Nat.Primes) => 0).toProfinite.toTop →ₜ* ↑(ProfiniteGrp.primewisePadicProcyclicModel fun (x : Nat.Primes) => 0).toProfinite.toTop, f (ProfiniteGrp.primewisePadicRealizationGenerator fun (x : Nat.Primes) => 0) = 1
```

**Original catalogue explanation (not a Lean docstring):** A zero source exponent permits the specified trivial-target image.

[Source](../Tests/ProcyclicHom.lean#L234) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.topSourceToArbitrary

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.topSourceToArbitrary (H : ProfiniteGrp.{v}) (h : ↑H.toProfinite.toTop) : ∃! f : ↑(ProfiniteGrp.primewisePadicProcyclicModel fun (x : Nat.Primes) => ⊤).toProfinite.toTop →ₜ* ↑H.toProfinite.toTop, f (ProfiniteGrp.primewisePadicRealizationGenerator fun (x : Nat.Primes) => ⊤) = h
```

**Original catalogue explanation (not a Lean docstring):** The all-infinite source profile admits a unique continuous homomorphism with any prescribed target element as the image of its generator.

[Source](../Tests/ProcyclicHom.lean#L247) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.mixedProfile

Kind: `def`.

```lean
def ProcyclicHomTests.mixedProfile (p : Nat.Primes) : ℕ∞
```

**Native source docstring:** A profile with zero, positive finite and infinite primewise coordinates.

[Source](../Tests/ProcyclicHom.lean#L258) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.smallerMixedProfile

Kind: `def`.

```lean
def ProcyclicHomTests.smallerMixedProfile (p : Nat.Primes) : ℕ∞
```

**Native source docstring:** A smaller profile used to test the direction of the Hom inequality.

[Source](../Tests/ProcyclicHom.lean#L261) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.mixedProfileQuotient

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.mixedProfileQuotient : ∃ (f : ↑(ProfiniteGrp.primewisePadicProcyclicModel mixedProfile).toProfinite.toTop →ₜ* ↑(ProfiniteGrp.primewisePadicProcyclicModel smallerMixedProfile).toProfinite.toTop), Function.Surjective ⇑f
```

**Original catalogue explanation (not a Lean docstring):** Checks the pointwise admissibility condition for mixed source and target exponents.

[Source](../Tests/ProcyclicHom.lean#L265) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.identityAndComposition

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.identityAndComposition (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (K : ProfiniteGrp.{w}) (hG : G.IsProcyclic) (hH : H.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) (hh : H.IsTopologicalGenerator h) (k : ↑K.toProfinite.toTop) (ha : ∀ (p : Nat.Primes), ProfiniteGrp.primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p) (hb : ∀ (p : Nat.Primes), ProfiniteGrp.primewisePadicKernelExponents (K.primewisePadicBaseMapOfGenerator k) p ≤ hH.exponents p) : (ProfiniteGrp.factorOfGenerator hH h hh k hb).comp (ProfiniteGrp.factorOfGenerator hG g hg h ha) = ProfiniteGrp.factorOfGenerator hG g hg k ⋯
```

**Original catalogue explanation (not a Lean docstring):** Checks composition of the prescribed-generator-image factor maps.

[Source](../Tests/ProcyclicHom.lean#L276) (native source start line; generated entries may point to their parent).

#### ProcyclicHomTests.identityEvaluation

Kind: `theorem`.

```lean
theorem ProcyclicHomTests.identityEvaluation (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : ProfiniteGrp.factorOfGenerator hG g hg g ⋯ = ContinuousMonoidHom.id ↑G.toProfinite.toTop
```

**Original catalogue explanation (not a Lean docstring):** The generator-image construction sends the identity map to the given generator.

[Source](../Tests/ProcyclicHom.lean#L291) (native source start line; generated entries may point to their parent).

### Tests.ProcyclicInvariant

16 native named entries; 0 native instance-table rows.

#### ProcyclicInvariantTests.arbitraryGenerators

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.arbitraryGenerators (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g h : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (hh : G.IsTopologicalGenerator h) : G.primewisePadicExponentsOfGenerator g = G.primewisePadicExponentsOfGenerator h
```

**Original catalogue explanation (not a Lean docstring):** Exponents computed from different supplied generators agree.

[Source](../Tests/ProcyclicInvariant.lean#L25) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.independentProofs

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.independentProofs (G : ProfiniteGrp.{u}) (hG hG' : G.IsProcyclic) : hG.exponents = hG'.exponents
```

**Original catalogue explanation (not a Lean docstring):** The exponent invariant is independent of which procyclicity witness is supplied.

[Source](../Tests/ProcyclicInvariant.lean#L34) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.fixedBase

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.fixedBase (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) : hG.exponents = ProfiniteGrp.primewisePadicKernelExponents (G.primewisePadicBaseMapOfGenerator g)
```

**Original catalogue explanation (not a Lean docstring):** The chosen base map computes the group exponent family.

[Source](../Tests/ProcyclicInvariant.lean#L38) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.model

Kind: `def`.

```lean
noncomputable def ProcyclicInvariantTests.model (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) : ↑G.toProfinite.toTop ≃ₜ* Multiplicative ↑(ProfiniteGrp.primewisePadicQuotientModel hG.exponents).toProfinite.toTop
```

**Native source docstring:** The generator-independent primewise quotient model of a procyclic group.

[Source](../Tests/ProcyclicInvariant.lean#L44) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.forward

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.forward (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (hG : G.IsProcyclic) (hH : H.IsProcyclic) (e : ↑G.toProfinite.toTop ≃ₜ* ↑H.toProfinite.toTop) : hG.exponents = hH.exponents
```

**Original catalogue explanation (not a Lean docstring):** A continuous equivalence preserves the exponent family.

[Source](../Tests/ProcyclicInvariant.lean#L49) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.backward

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.backward (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (hG : G.IsProcyclic) (hH : H.IsProcyclic) (heq : hG.exponents = hH.exponents) : Nonempty (↑G.toProfinite.toTop ≃ₜ* ↑H.toProfinite.toTop)
```

**Original catalogue explanation (not a Lean docstring):** Equal exponent families construct a continuous group equivalence.

[Source](../Tests/ProcyclicInvariant.lean#L54) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.positiveUniverseEquiv

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.positiveUniverseEquiv (G : ProfiniteGrp.{1}) (H : ProfiniteGrp.{2}) (hG : G.IsProcyclic) (hH : H.IsProcyclic) (e : ↑G.toProfinite.toTop ≃ₜ* ↑H.toProfinite.toTop) : hG.exponents = hH.exponents
```

**Original catalogue explanation (not a Lean docstring):** The equivalence criterion works across independent positive universes.

[Source](../Tests/ProcyclicInvariant.lean#L59) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.independentKernel

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.independentKernel {Y : Type u} {Z : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y] [Group Z] [TopologicalSpace Z] [T1Space Z] (f : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop →ₜ* Y) (j : Y →ₜ* Z) (hj : Function.Injective ⇑j) : ProfiniteGrp.primewisePadicKernelIdeal (j.comp f) = ProfiniteGrp.primewisePadicKernelIdeal f
```

**Original catalogue explanation (not a Lean docstring):** Injective postcomposition into a T1 topological group preserves the primewise kernel ideal.

[Source](../Tests/ProcyclicInvariant.lean#L65) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.subsingletonZero

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.subsingletonZero (G : ProfiniteGrp.{u}) [Subsingleton ↑G.toProfinite.toTop] (hG : G.IsProcyclic) (p : Nat.Primes) : hG.exponents p = 0
```

**Original catalogue explanation (not a Lean docstring):** The trivial profinite group has the zero exponent family.

[Source](../Tests/ProcyclicInvariant.lean#L74) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.baseMapPrimewiseGenerator

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.baseMapPrimewiseGenerator : ProfiniteGrp.primewisePadic.primewisePadicBaseMapOfGenerator ProfiniteGrp.primewisePadicGenerator = ↑ProfiniteGrp.primewisePadicChangeUniverse
```

**Original catalogue explanation (not a Lean docstring):** The canonical primewise image of the integer generator has the expected profile.

[Source](../Tests/ProcyclicInvariant.lean#L85) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.primewiseTop

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.primewiseTop (p : Nat.Primes) : ProfiniteGrp.primewisePadic_isProcyclic.exponents p = ⊤
```

**Original catalogue explanation (not a Lean docstring):** The unquotiented primewise product has infinite exponent at each prime.

[Source](../Tests/ProcyclicInvariant.lean#L108) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.cyclicTwelveCompatibility

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.cyclicTwelveCompatibility : ⋯.exponents = (ProfiniteGrp.finiteCyclic 12).primewisePadicExponentsOfGenerator (ProfiniteGrp.finiteCyclicGenerator 12)
```

**Original catalogue explanation (not a Lean docstring):** The order-twelve cyclic group's invariant agrees with the exponent family computed from its supplied generator.

[Source](../Tests/ProcyclicInvariant.lean#L116) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.cyclicTwoNontrivial

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.cyclicTwoNontrivial : ProfiniteGrp.finiteCyclicGenerator 2 ≠ 1
```

**Original catalogue explanation (not a Lean docstring):** The cyclic group of order two is not trivial.

[Source](../Tests/ProcyclicInvariant.lean#L123) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.cyclicTwoExponentsNonzero

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.cyclicTwoExponentsNonzero : ⋯.exponents ≠ fun (x : Nat.Primes) => 0
```

**Original catalogue explanation (not a Lean docstring):** Its primewise exponent family is not everywhere zero.

[Source](../Tests/ProcyclicInvariant.lean#L128) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.cyclicTwoNotEquivalentToSingleton

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.cyclicTwoNotEquivalentToSingleton : ¬Nonempty (↑(ProfiniteGrp.finiteCyclic 2).toProfinite.toTop ≃ₜ* ↑(ProfiniteGrp.finiteCyclic 1).toProfinite.toTop)
```

**Original catalogue explanation (not a Lean docstring):** The nontrivial cyclic group cannot be continuously equivalent to the singleton group.

[Source](../Tests/ProcyclicInvariant.lean#L147) (native source start line; generated entries may point to their parent).

#### ProcyclicInvariantTests.primewiseNotEquivalentToSingleton

Kind: `theorem`.

```lean
theorem ProcyclicInvariantTests.primewiseNotEquivalentToSingleton : ¬Nonempty (↑ProfiniteGrp.primewisePadic.toProfinite.toTop ≃ₜ* ↑(ProfiniteGrp.ofFiniteGrp ↧PUnit.{2}).toProfinite.toTop)
```

**Original catalogue explanation (not a Lean docstring):** The infinite-profile primewise group cannot be continuously equivalent to the singleton group.

[Source](../Tests/ProcyclicInvariant.lean#L162) (native source start line; generated entries may point to their parent).

### Tests.ProcyclicPower

15 native named entries; 0 native instance-table rows.

#### ProcyclicPowerTest.power_hom_application

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.power_hom_application (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (x : ↑G.toProfinite.toTop) : (G.powerHom hG n) x = x ^ n
```

**Original catalogue explanation (not a Lean docstring):** The power map sends a concrete element to its chosen natural-number power.

[Source](../Tests/ProcyclicPower.lean#L26) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.proof_parameter_independence

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.proof_parameter_independence (G : ProfiniteGrp.{u}) (hG kG : G.IsProcyclic) (n : ℕ) : G.powerHom hG n = G.powerHom kG n ∧ G.powerImage hG n = G.powerImage kG n
```

**Original catalogue explanation (not a Lean docstring):** The power image does not depend on the chosen proof of procyclicity.

[Source](../Tests/ProcyclicPower.lean#L29) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.zero_and_one

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.zero_and_one (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) : ↑(G.powerImage hG 0) = ⊥ ∧ ↑(G.powerImage hG 1) = ⊤
```

**Original catalogue explanation (not a Lean docstring):** Zero-th and first power images are respectively the bottom and top subgroup.

[Source](../Tests/ProcyclicPower.lean#L34) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.open_and_divides

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.open_and_divides (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (hn : 0 < n) : IsOpen ↑↑(G.powerImage hG n) ∧ (↑(G.powerImage hG n)).index ∣ n
```

**Original catalogue explanation (not a Lean docstring):** For a positive power the open image has index dividing, not necessarily equal to, the power.

[Source](../Tests/ProcyclicPower.lean#L39) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.subgroup_generator

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.subgroup_generator (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℕ) : ↑(G.powerImage hG n) = (Subgroup.zpowers (g ^ n)).topologicalClosure ∧ (ProfiniteGrp.ofClosedSubgroup (G.powerImage hG n)).IsTopologicalGenerator ((G.powerHomToImage hG n) g)
```

**Original catalogue explanation (not a Lean docstring):** The power of a supplied generator generates the power-image subgroup.

[Source](../Tests/ProcyclicPower.lean#L45) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.quotient_generator

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.quotient_generator (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℕ) (hn : 0 < n) : IsCyclic (↑G.toProfinite.toTop ⧸ ↑(G.powerImage hG n)) ∧ Finite (↑G.toProfinite.toTop ⧸ ↑(G.powerImage hG n)) ∧ Subgroup.zpowers ((QuotientGroup.mk' ↑(G.powerImage hG n)) g) = ⊤
```

**Original catalogue explanation (not a Lean docstring):** Its class generates the finite cyclic quotient by a positive-power image.

[Source](../Tests/ProcyclicPower.lean#L54) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.all_open

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.all_open (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (H : OpenSubgroup ↑G.toProfinite.toTop) : ↑H = ↑(G.powerImage hG (↑H).index)
```

**Original catalogue explanation (not a Lean docstring):** Every open subgroup is presented by its index-th power image.

[Source](../Tests/ProcyclicPower.lean#L63) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.subgroup_bridge

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.subgroup_bridge (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (H : Subgroup ↑G.toProfinite.toTop) (hH : IsOpen ↑H) : H = ↑(G.powerImage hG H.index)
```

**Original catalogue explanation (not a Lean docstring):** An ordinary open subgroup agrees with the matching power image.

[Source](../Tests/ProcyclicPower.lean#L67) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.equal_index_unique

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.equal_index_unique (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (H K : OpenSubgroup ↑G.toProfinite.toTop) (hidx : (↑H).index = (↑K).index) : H = K
```

**Original catalogue explanation (not a Lean docstring):** Open subgroups of a procyclic group with the same index are equal.

[Source](../Tests/ProcyclicPower.lean#L71) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.open_membership

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.open_membership (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (hn : 0 < n) (x : ↑G.toProfinite.toTop) (hx : x ∈ G.powerOpenSubgroup hG n hn) : ∃ (y : ↑G.toProfinite.toTop), y ^ n = x
```

**Original catalogue explanation (not a Lean docstring):** Membership in a positive-power open image supplies a concrete power root.

[Source](../Tests/ProcyclicPower.lean#L75) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.two_fourth_index

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.two_fourth_index : (↑((ProfiniteGrp.finiteCyclic 2).powerImage ⋯ 4)).index = 2
```

**Original catalogue explanation (not a Lean docstring):** Fourth powers in the cyclic group of order two have index two, not four.

[Source](../Tests/ProcyclicPower.lean#L123) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.three_square_index

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.three_square_index : (↑((ProfiniteGrp.finiteCyclic 3).powerImage ⋯ 2)).index = 1
```

**Original catalogue explanation (not a Lean docstring):** Squares in the cyclic group of order three are surjective and have index one.

[Source](../Tests/ProcyclicPower.lean#L138) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.four_square_index

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.four_square_index : (↑((ProfiniteGrp.finiteCyclic 4).powerImage ⋯ 2)).index = 2
```

**Original catalogue explanation (not a Lean docstring):** Squares in the cyclic group of order four have index two.

[Source](../Tests/ProcyclicPower.lean#L146) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.four_square_nontrivial

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.four_square_nontrivial : ∃ x ∈ (ProfiniteGrp.finiteCyclic 4).powerImage ⋯ 2, x ≠ 1
```

**Original catalogue explanation (not a Lean docstring):** The squares in the cyclic group of order four include a nonidentity element.

[Source](../Tests/ProcyclicPower.lean#L169) (native source start line; generated entries may point to their parent).

#### ProcyclicPowerTest.trivial_power_top

Kind: `theorem`.

```lean
theorem ProcyclicPowerTest.trivial_power_top : ↑((ProfiniteGrp.ofFiniteGrp ↧PUnit.{u_1 + 1}).powerImage ProfiniteGrp.punit_isProcyclic 7) = ⊤
```

**Original catalogue explanation (not a Lean docstring):** The seventh-power image of the trivial group is the top subgroup.

[Source](../Tests/ProcyclicPower.lean#L176) (native source start line; generated entries may point to their parent).

### Tests.ProcyclicQuotient

4 native named entries; 0 native instance-table rows.

#### mixedPrimewiseMap

Kind: `def`.

```lean
noncomputable def mixedPrimewiseMap : ↑ProfiniteGrp.primewisePadic.toProfinite.toTop →ₜ* Multiplicative ↑(ProfiniteGrp.primewisePadicQuotientModel mixedExponents).toProfinite.toTop
```

**Native source docstring:** The mixed quotient map used by both quotient and generator-independence clients.

[Source](../Tests/ProcyclicQuotient.lean#L153) (native source start line; generated entries may point to their parent).

#### mixedPrimewiseMap_mk

Kind: `theorem`.

```lean
theorem mixedPrimewiseMap_mk (x : ProfiniteGrp.primewisePadicRing) : mixedPrimewiseMap (ProfiniteGrp.primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) = Multiplicative.ofAdd ((ProfiniteGrp.primewisePadicQuotientContinuousAddEquivModel mixedExponents) ((Ideal.Quotient.mk (ProfiniteGrp.primewisePadicIdealOfExponents mixedExponents)) x))
```

**Native source docstring:** The mixed quotient has zero, positive finite, and top exponents.

[Source](../Tests/ProcyclicQuotient.lean#L174) (native source start line; generated entries may point to their parent).

#### mixedPrimewiseMap_surjective

Kind: `theorem`.

```lean
theorem mixedPrimewiseMap_surjective : Function.Surjective ⇑mixedPrimewiseMap
```

**Original catalogue explanation (not a Lean docstring):** A mixed finite/infinite/zero coordinate quotient map is surjective.

[Source](../Tests/ProcyclicQuotient.lean#L184) (native source start line; generated entries may point to their parent).

#### mixedPrimewiseMap_kernelIdeal

Kind: `theorem`.

```lean
theorem mixedPrimewiseMap_kernelIdeal : ProfiniteGrp.primewisePadicKernelIdeal mixedPrimewiseMap = ProfiniteGrp.primewisePadicIdealOfExponents mixedExponents
```

**Original catalogue explanation (not a Lean docstring):** The mixed quotient map has the declared primewise kernel ideal.

[Source](../Tests/ProcyclicQuotient.lean#L191) (native source start line; generated entries may point to their parent).

### Tests.ProcyclicRealization

26 native named entries; 0 native instance-table rows.

#### ProcyclicRealizationTests.instFactPrimeValNat_tests

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.instFactPrimeValNat_tests (p : Nat.Primes) : Fact (Nat.Prime ↑p)
```

**Original catalogue explanation (not a Lean docstring):** A module-local generated instance supplies primality evidence carried by a prime-indexed value; it is not a public API promise.

[Source](../Tests/ProcyclicRealization.lean#L23) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.instFactPrimeOfNatNat_tests

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.instFactPrimeOfNatNat_tests : Fact (Nat.Prime 5)
```

**Original catalogue explanation (not a Lean docstring):** A local test instance supplies primality of the concrete prime five for residue computations.

[Source](../Tests/ProcyclicRealization.lean#L24) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.arbitraryMap

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.arbitraryMap (e : Nat.Primes → ℕ∞) : Function.Surjective ⇑(ProfiniteGrp.primewisePadicRealizationMap e)
```

**Original catalogue explanation (not a Lean docstring):** The canonical realization map is surjective for every primewise exponent family.

[Source](../Tests/ProcyclicRealization.lean#L26) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.arbitraryActualKernel

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.arbitraryActualKernel (e : Nat.Primes → ℕ∞) : ProfiniteGrp.primewisePadicKernelIdeal (ProfiniteGrp.primewisePadicRealizationMap e) = ProfiniteGrp.primewisePadicIdealOfExponents e
```

**Original catalogue explanation (not a Lean docstring):** The realized map's kernel ideal is the ideal prescribed by its exponent family.

[Source](../Tests/ProcyclicRealization.lean#L30) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.arbitraryExtractedKernel

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.arbitraryExtractedKernel (e : Nat.Primes → ℕ∞) : ProfiniteGrp.primewisePadicKernelExponents (ProfiniteGrp.primewisePadicRealizationMap e) = e
```

**Original catalogue explanation (not a Lean docstring):** The computed kernel exponents of a realization map recover the input family.

[Source](../Tests/ProcyclicRealization.lean#L35) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.arbitraryRepresentative

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.arbitraryRepresentative (e : Nat.Primes → ℕ∞) (x : ProfiniteGrp.primewisePadicRing) (p : Nat.Primes) : Multiplicative.toAdd ((ProfiniteGrp.primewisePadicRealizationMap e) (ProfiniteGrp.primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x))) p = (ProfiniteGrp.liftedPadicQuotientContinuousAddEquivFactor p (e p)) ((Ideal.Quotient.mk (ProfiniteGrp.liftedPadicIdealOfExponent p (e p))) (x p))
```

**Original catalogue explanation (not a Lean docstring):** Computes each coordinate of the realization map on an arbitrary ring representative.

[Source](../Tests/ProcyclicRealization.lean#L39) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.arbitraryGenerator

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.arbitraryGenerator (e : Nat.Primes → ℕ∞) : (ProfiniteGrp.primewisePadicProcyclicModel e).IsTopologicalGenerator (ProfiniteGrp.primewisePadicRealizationGenerator e)
```

**Original catalogue explanation (not a Lean docstring):** The distinguished image of the integer is a topological generator.

[Source](../Tests/ProcyclicRealization.lean#L47) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.arbitraryInvariant

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.arbitraryInvariant (e : Nat.Primes → ℕ∞) (h : (ProfiniteGrp.primewisePadicProcyclicModel e).IsProcyclic) : h.exponents = e
```

**Original catalogue explanation (not a Lean docstring):** The realized group's exponent invariant equals the prescribed family.

[Source](../Tests/ProcyclicRealization.lean#L52) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.arbitraryPositiveUniverseExists

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.arbitraryPositiveUniverseExists (e : Nat.Primes → ℕ∞) : ∃ (G : ProfiniteGrp.{1}) (hG : G.IsProcyclic), hG.exponents = e
```

**Original catalogue explanation (not a Lean docstring):** The realization construction works in a positive universe.

[Source](../Tests/ProcyclicRealization.lean#L57) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.arbitraryIndependentUniverseEquiv

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.arbitraryIndependentUniverseEquiv (e f : Nat.Primes → ℕ∞) : Nonempty (↑(ProfiniteGrp.primewisePadicProcyclicModel e).toProfinite.toTop ≃ₜ* ↑(ProfiniteGrp.primewisePadicProcyclicModel f).toProfinite.toTop) ↔ e = f
```

**Original catalogue explanation (not a Lean docstring):** Equivalent exponent profiles produce models across independent universes.

[Source](../Tests/ProcyclicRealization.lean#L61) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.allZeroKernel

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.allZeroKernel : ProfiniteGrp.primewisePadicKernelIdeal (ProfiniteGrp.primewisePadicRealizationMap fun (x : Nat.Primes) => 0) = ⊤
```

**Original catalogue explanation (not a Lean docstring):** An all-zero profile has the full primewise ideal as its kernel.

[Source](../Tests/ProcyclicRealization.lean#L66) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.allZeroInvariant

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.allZeroInvariant : ⋯.exponents = fun (x : Nat.Primes) => 0
```

**Original catalogue explanation (not a Lean docstring):** The corresponding quotient has zero exponent at every prime.

[Source](../Tests/ProcyclicRealization.lean#L72) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.allZeroTrivial

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.allZeroTrivial (x : ↑(ProfiniteGrp.primewisePadicProcyclicModel fun (x : Nat.Primes) => 0).toProfinite.toTop) : x = 1
```

**Original catalogue explanation (not a Lean docstring):** The all-zero realization is a trivial profinite group.

[Source](../Tests/ProcyclicRealization.lean#L77) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.allTopInvariant

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.allTopInvariant : ⋯.exponents = fun (x : Nat.Primes) => ⊤
```

**Original catalogue explanation (not a Lean docstring):** The all-infinite realization has the infinite exponent profile.

[Source](../Tests/ProcyclicRealization.lean#L92) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.allTopGeneratorCoordinate

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.allTopGeneratorCoordinate (p : Nat.Primes) : Multiplicative.toAdd (ProfiniteGrp.primewisePadicRealizationGenerator fun (x : Nat.Primes) => ⊤) p = { down := 1 }
```

**Original catalogue explanation (not a Lean docstring):** The all-infinite model's canonical generator has the stated coordinate value.

[Source](../Tests/ProcyclicRealization.lean#L97) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.allTopGeneratorNotIdentity

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.allTopGeneratorNotIdentity : (ProfiniteGrp.primewisePadicRealizationGenerator fun (x : Nat.Primes) => ⊤) ≠ 1
```

**Original catalogue explanation (not a Lean docstring):** The all-infinite model's chosen generator is not the identity.

[Source](../Tests/ProcyclicRealization.lean#L104) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.positiveFiniteGeneratorCoordinate

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.positiveFiniteGeneratorCoordinate (p : Nat.Primes) : Multiplicative.toAdd (ProfiniteGrp.primewisePadicRealizationGenerator fun (x : Nat.Primes) => 2) p = { down := 1 }
```

**Original catalogue explanation (not a Lean docstring):** The finite positive coordinate of the canonical generator has its expected residue.

[Source](../Tests/ProcyclicRealization.lean#L114) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.positiveFiniteInvariant

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.positiveFiniteInvariant : ⋯.exponents = fun (x : Nat.Primes) => 2
```

**Original catalogue explanation (not a Lean docstring):** A positive finite exponent contributes that exact primewise invariant.

[Source](../Tests/ProcyclicRealization.lean#L123) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.positiveFiniteGeneratorNotIdentity

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.positiveFiniteGeneratorNotIdentity : (ProfiniteGrp.primewisePadicRealizationGenerator fun (x : Nat.Primes) => 2) ≠ 1
```

**Original catalogue explanation (not a Lean docstring):** The positive finite coordinate prevents the canonical generator being the identity.

[Source](../Tests/ProcyclicRealization.lean#L128) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.mixed

Kind: `def`.

```lean
def ProcyclicRealizationTests.mixed (p : Nat.Primes) : ℕ∞
```

**Native source docstring:** A realization profile combining zero, positive finite and top coordinates.

[Source](../Tests/ProcyclicRealization.lean#L138) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.mixedValues

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.mixedValues : mixed ⟨2, mixedValues._proof_1⟩ = 0 ∧ mixed ⟨3, mixedValues._proof_2⟩ = 2 ∧ mixed ⟨5, mixedValues._proof_3⟩ = ⊤
```

**Original catalogue explanation (not a Lean docstring):** The mixed profile assigns respectively zero, finite and infinite coordinate exponents.

[Source](../Tests/ProcyclicRealization.lean#L142) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.mixedZeroCoordinate

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.mixedZeroCoordinate : Multiplicative.toAdd ((ProfiniteGrp.primewisePadicRealizationMap mixed) (ProfiniteGrp.primewisePadicDiagonal 1)) ⟨2, mixedValues._proof_1⟩ ≍ { down := 1 }
```

**Original catalogue explanation (not a Lean docstring):** The zero-exponent coordinate of a mixed realization is trivial.

[Source](../Tests/ProcyclicRealization.lean#L148) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.mixedFiniteCoordinate

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.mixedFiniteCoordinate : Multiplicative.toAdd ((ProfiniteGrp.primewisePadicRealizationMap mixed) (ProfiniteGrp.primewisePadicDiagonal 1)) ⟨3, mixedValues._proof_2⟩ ≍ { down := 1 }
```

**Original catalogue explanation (not a Lean docstring):** The finite positive coordinate has its expected residue model.

[Source](../Tests/ProcyclicRealization.lean#L155) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.mixedTopCoordinate

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.mixedTopCoordinate : Multiplicative.toAdd ((ProfiniteGrp.primewisePadicRealizationMap mixed) (ProfiniteGrp.primewisePadicDiagonal 1)) ⟨5, mixedValues._proof_3⟩ ≍ { down := 1 }
```

**Original catalogue explanation (not a Lean docstring):** The infinite coordinate retains its full p-adic model.

[Source](../Tests/ProcyclicRealization.lean#L162) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.mixedInvariant

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.mixedInvariant : ⋯.exponents = mixed
```

**Original catalogue explanation (not a Lean docstring):** The mixed realization's invariant recovers its full input family.

[Source](../Tests/ProcyclicRealization.lean#L168) (native source start line; generated entries may point to their parent).

#### ProcyclicRealizationTests.unequalProfilesNoEquiv

Kind: `theorem`.

```lean
theorem ProcyclicRealizationTests.unequalProfilesNoEquiv : ¬Nonempty (↑(ProfiniteGrp.primewisePadicProcyclicModel mixed).toProfinite.toTop ≃ₜ* ↑(ProfiniteGrp.primewisePadicProcyclicModel fun (x : Nat.Primes) => ⊤).toProfinite.toTop)
```

**Original catalogue explanation (not a Lean docstring):** Different primewise exponent families cannot produce equivalent realized groups.

[Source](../Tests/ProcyclicRealization.lean#L172) (native source start line; generated entries may point to their parent).

### Tests.ProcyclicTorsionFree

0 native named entries; 0 native instance-table rows.

No new named declarations in this module.

### Tests.PublicRoot

18 native named entries; 0 native instance-table rows.

#### PublicRootTests.arbitraryTargetCriterion

Kind: `theorem`.

```lean
theorem PublicRootTests.arbitraryTargetCriterion (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v}) (hG : G.IsProcyclic) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (h : ↑H.toProfinite.toTop) : (∃! f : ↑G.toProfinite.toTop →ₜ* ↑H.toProfinite.toTop, f g = h) ↔ ∀ (p : Nat.Primes), ProfiniteGrp.primewisePadicKernelExponents (H.primewisePadicBaseMapOfGenerator h) p ≤ hG.exponents p
```

**Native source docstring:** The prescribed-image criterion makes no procyclicity assumption on the target.

[Source](../Tests/PublicRoot.lean#L25) (native source start line; generated entries may point to their parent).

#### PublicRootTests.positivePowerIndexDivides

Kind: `theorem`.

```lean
theorem PublicRootTests.positivePowerIndexDivides (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (n : ℕ) (hn : 0 < n) : IsOpen ↑↑(G.powerImage hG n) ∧ (↑(G.powerImage hG n)).index ∣ n
```

**Native source docstring:** A positive power image is open and has index dividing, not necessarily equal to, `n`.

[Source](../Tests/PublicRoot.lean#L33) (native source start line; generated entries may point to their parent).

#### PublicRootTests.cyclicTwoFourthIndexDivides

Kind: `theorem`.

```lean
theorem PublicRootTests.cyclicTwoFourthIndexDivides : (↑((ProfiniteGrp.finiteCyclic 2).powerImage ⋯ 4)).index ∣ 4
```

**Native source docstring:** A root-import consumer obtains the fourth-power index divisibility for a
finite cyclic group. The exact smaller index is tested in `Tests.ProcyclicPower`.

[Source](../Tests/PublicRoot.lean#L40) (native source start line; generated entries may point to their parent).

#### PublicRootTests.mixedProfile

Kind: `def`.

```lean
def PublicRootTests.mixedProfile (p : Nat.Primes) : ℕ∞
```

**Native source docstring:** Zero, positive finite and infinite exponents occur in one model.

[Source](../Tests/PublicRoot.lean#L47) (native source start line; generated entries may point to their parent).

#### PublicRootTests.mixedProfileExtracted

Kind: `theorem`.

```lean
theorem PublicRootTests.mixedProfileExtracted : ProfiniteGrp.primewisePadicKernelExponents (ProfiniteGrp.primewisePadicRealizationMap mixedProfile) = mixedProfile
```

**Native source docstring:** Extracting the kernel profile recovers the original mixed family.

[Source](../Tests/PublicRoot.lean#L51) (native source start line; generated entries may point to their parent).

#### PublicRootTests.mixedProfileCoordinates

Kind: `theorem`.

```lean
theorem PublicRootTests.mixedProfileCoordinates : ProfiniteGrp.primewisePadicKernelExponents (ProfiniteGrp.primewisePadicRealizationMap mixedProfile) ⟨2, mixedProfileCoordinates._proof_1⟩ = 0 ∧ ProfiniteGrp.primewisePadicKernelExponents (ProfiniteGrp.primewisePadicRealizationMap mixedProfile) ⟨3, mixedProfileCoordinates._proof_2⟩ = 2 ∧ ProfiniteGrp.primewisePadicKernelExponents (ProfiniteGrp.primewisePadicRealizationMap mixedProfile) ⟨5, mixedProfileCoordinates._proof_3⟩ = ⊤
```

**Native source docstring:** The model realizes the three distinct exponent regimes at concrete primes.

[Source](../Tests/PublicRoot.lean#L57) (native source start line; generated entries may point to their parent).

#### PublicRootTests.zeroAndTopProfiles

Kind: `theorem`.

```lean
theorem PublicRootTests.zeroAndTopProfiles : (ProfiniteGrp.primewisePadicKernelExponents (ProfiniteGrp.primewisePadicRealizationMap fun (x : Nat.Primes) => 0) = fun (x : Nat.Primes) => 0) ∧ ProfiniteGrp.primewisePadicKernelExponents (ProfiniteGrp.primewisePadicRealizationMap fun (x : Nat.Primes) => ⊤) = fun (x : Nat.Primes) => ⊤
```

**Native source docstring:** Uniform zero and top profiles are recovered, without identifying source integers.

[Source](../Tests/PublicRoot.lean#L71) (native source start line; generated entries may point to their parent).

#### PublicRootTests.completionIntegerSimp

Kind: `theorem`.

```lean
theorem PublicRootTests.completionIntegerSimp (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (n : ℤ) : (ProfiniteGrp.Hom.hom (G.integerCompletionMap g)) (ProfiniteGrp.ProfiniteCompletion.etaFn ↧(ULift.{u, 0} (Multiplicative ℤ)) { down := Multiplicative.ofAdd n }) = g ^ n
```

**Native source docstring:** The completion-map integer computation still follows from plain `simp`.

[Source](../Tests/PublicRoot.lean#L82) (native source start line; generated entries may point to their parent).

#### PublicRootTests.completionEquivIntegerSimp

Kind: `theorem`.

```lean
theorem PublicRootTests.completionEquivIntegerSimp (n : ℤ) : ProfiniteGrp.integerCompletionEquivPrimewisePadic (ProfiniteGrp.ProfiniteCompletion.etaFn ↧(ULift.{u, 0} (Multiplicative ℤ)) { down := Multiplicative.ofAdd n }) = ProfiniteGrp.primewisePadicDiagonal n
```

**Native source docstring:** The primewise equivalence's integer computation needs no special simp rule.

[Source](../Tests/PublicRoot.lean#L90) (native source start line; generated entries may point to their parent).

#### PublicRootTests.universeIntegerSimp

Kind: `theorem`.

```lean
theorem PublicRootTests.universeIntegerSimp (n : ℤ) : ProfiniteGrp.primewisePadicRingChangeUniverse ↑n = ↑n
```

**Native source docstring:** Cross-universe integer casts use the general ring-hom simp rule.

[Source](../Tests/PublicRoot.lean#L98) (native source start line; generated entries may point to their parent).

#### PublicRootTests.zeroOnePowerSimp

Kind: `theorem`.

```lean
theorem PublicRootTests.zeroOnePowerSimp (G : ProfiniteGrp.{u}) (hG : G.IsProcyclic) (x : ↑G.toProfinite.toTop) : (G.powerHom hG 0) x = 1 ∧ (G.powerHom hG 1) x = x
```

**Native source docstring:** Plain `simp` retains both zero- and one-power computations.

[Source](../Tests/PublicRoot.lean#L104) (native source start line; generated entries may point to their parent).

#### PublicRootTests.powerCoordinatesSimp

Kind: `theorem`.

```lean
theorem PublicRootTests.powerCoordinatesSimp (G : ProfiniteGrp.{u}) (g : ↑G.toProfinite.toTop) (hg : G.IsTopologicalGenerator g) (n : ℤ) (p : Nat.Primes) : Multiplicative.toAdd ((G.procyclicContinuousMulEquivModel g hg) (g ^ n)) p = (ProfiniteGrp.liftedPadicQuotientContinuousAddEquivFactor p (G.primewisePadicExponentsOfGenerator g p)) ((Ideal.Quotient.mk (ProfiniteGrp.liftedPadicIdealOfExponent p (G.primewisePadicExponentsOfGenerator g p))) (Multiplicative.toAdd (ProfiniteGrp.primewisePadicRingMultiplicativeEquiv.symm (ProfiniteGrp.primewisePadicDiagonal n)) p))
```

**Native source docstring:** The original power-coordinate proposition is still solved by plain `simp`.

[Source](../Tests/PublicRoot.lean#L109) (native source start line; generated entries may point to their parent).

#### PublicRootTests.arbitraryTopologyStageInjective

Kind: `theorem`.

```lean
theorem PublicRootTests.arbitraryTopologyStageInjective (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] (U : ProfiniteGrp.FiniteQuotientHom.StageIndex G) : Function.Injective (ProfiniteGrp.FiniteQuotientHom.stageToContinuousHom G F U)
```

**Native source docstring:** Finite-stage interpretation is valid for an arbitrary topology on the target.

[Source](../Tests/PublicRoot.lean#L122) (native source start line; generated entries may point to their parent).

#### PublicRootTests.arbitraryTopologyColimitInjective

Kind: `theorem`.

```lean
theorem PublicRootTests.arbitraryTopologyColimitInjective (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] : Function.Injective (ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom G F)
```

**Native source docstring:** The colimit's forward map needs no discreteness or topological-group law.

[Source](../Tests/PublicRoot.lean#L129) (native source start line; generated entries may point to their parent).

#### PublicRootTests.stagePayloadUnchanged

Kind: `theorem`.

```lean
theorem PublicRootTests.stagePayloadUnchanged (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] (U : ProfiniteGrp.FiniteQuotientHom.StageIndex G) (a : ProfiniteGrp.FiniteQuotientHom.HomStage G F U) : ProfiniteGrp.FiniteQuotientHom.stageToContinuousHom G F U a = let __MonoidHom := MonoidHom.comp a (QuotientGroup.mk' ↑(OrderDual.ofDual U).toOpenSubgroup); { toMonoidHom := __MonoidHom, continuous_toFun := ⋯ }
```

**Native source docstring:** Removing the unused target assumption did not change the defining payload.

[Source](../Tests/PublicRoot.lean#L135) (native source start line; generated entries may point to their parent).

#### PublicRootTests.discreteHomRoundTrip

Kind: `theorem`.

```lean
theorem PublicRootTests.discreteHomRoundTrip (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] [DiscreteTopology F] (f : ↑G.toProfinite.toTop →ₜ* F) : ProfiniteGrp.FiniteQuotientHom.HomColimit.toContinuousHom G F (ProfiniteGrp.FiniteQuotientHom.HomColimit.ofContinuousHom G F f) = f
```

**Native source docstring:** In the discrete case the original two-sided hom equivalence still applies.

[Source](../Tests/PublicRoot.lean#L146) (native source start line; generated entries may point to their parent).

#### PublicRootTests.arbitraryTopologyIdealTransport

Kind: `theorem`.

```lean
theorem PublicRootTests.arbitraryTopologyIdealTransport {R : Type u} [CommRing R] [TopologicalSpace R] {I J : Ideal R} (h : I = J) (x : R) : (Ideal.quotientContinuousAddEquivOfEq h) ((Ideal.Quotient.mk I) x) = (Ideal.Quotient.mk J) x
```

**Native source docstring:** Equality-of-ideals transport works without compatibility of topology and ring laws.

[Source](../Tests/PublicRoot.lean#L154) (native source start line; generated entries may point to their parent).

#### PublicRootTests.idealTransportPayloadUnchanged

Kind: `theorem`.

```lean
theorem PublicRootTests.idealTransportPayloadUnchanged {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) : Ideal.quotientContinuousAddEquivOfEq ⋯ = ContinuousAddEquiv.refl (R ⧸ I)
```

**Native source docstring:** Reflexive ideal transport retains its original definitional value.

[Source](../Tests/PublicRoot.lean#L162) (native source start line; generated entries may point to their parent).
