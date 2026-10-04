/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Finite-discrete presentations of topological spaces

A finite-discrete presentation uses a small cofiltered index category and a
homeomorphism to the explicit limit of a diagram of finite discrete spaces.
The topology on the limit is the subspace topology inherited from the product,
not an independently assigned topology. The cofiltered arrow convention is the
categorical form of an inverse system indexed by a filtered refinement order.

The index and its finite stages live in the universe of the carrier. This
includes the canonical `DiscreteQuotient` diagram for every carrier at that
universe; a larger index would require lifting the carrier to a maximum
universe in Mathlib's explicit limit construction.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, Lemma (1.1.1)
  (profinite spaces and finite discrete inverse limits).
- Mathlib, `Mathlib.Topology.Category.Profinite.AsLimit` and
  `Mathlib.CategoryTheory.Filtered.Basic` (finite-quotient presentation and filtered
  indices).
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- A presentation of a space as a cofiltered limit of finite discrete spaces. -/
structure FiniteDiscretePresentation (X : Type u) [TopologicalSpace X] where
  index : Type u
  [smallCategory : SmallCategory index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ FintypeCat.{u}
  equiv : X ≃ₜ (Profinite.limitCone (diagram ⋙ FintypeCat.toProfinite)).pt

attribute [instance] FiniteDiscretePresentation.smallCategory
  FiniteDiscretePresentation.cofiltered

namespace FiniteDiscretePresentation

variable {X : Type u} [TopologicalSpace X] (P : FiniteDiscretePresentation X)

/-- The presentation diagram, viewed as a diagram of topological spaces. -/
abbrev topDiagram : P.index ⥤ TopCat.{u} :=
  letI : SmallCategory P.index := P.smallCategory
  ((P.diagram ⋙ FintypeCat.toProfinite) ⋙ profiniteToCompHaus) ⋙ compHausToTop

/-- The finite discrete stage, regarded as a topological space. -/
abbrev stageSpace (j : P.index) : TopCat.{u} :=
  P.topDiagram.obj j

/-- The continuous projection from a presentation to a finite stage. -/
def stageMap (j : P.index) : C(X, P.stageSpace j) :=
  ⟨fun x => (P.equiv x).1 j,
    (continuous_apply j).comp (continuous_subtype_val.comp P.equiv.continuous)⟩

/-- The composite of the presentation homeomorphism with a limit projection. -/
def stage (j : P.index) : X → P.stageSpace j :=
  P.stageMap j

@[simp]
theorem stageMap_apply (j : P.index) (x : X) : P.stageMap j x = P.stage j x := rfl

@[simp]
theorem stage_apply (j : P.index) (x : X) : P.stage j x = (P.equiv x).1 j := rfl

/-- Presentation coordinates are continuous into the finite discrete stages. -/
theorem continuous_stage (j : P.index) : Continuous (P.stage j) :=
  (P.stageMap j).continuous

/-- Presentation coordinates commute with the transition maps. -/
@[simp]
theorem stage_naturality {j k : P.index} (f : j ⟶ k) (x : X) :
    (P.topDiagram.map f) (P.stage j x) = P.stage k x := by
  exact (P.equiv x).2 f

/-- The continuous stage projections form a cone over the topological diagram. -/
theorem stageMap_naturality {j k : P.index} (f : j ⟶ k) :
    (P.topDiagram.map f).hom.comp (P.stageMap j) = P.stageMap k := by
  ext x
  exact P.stage_naturality f x

/-- Finite-stage coordinates separate points, including when the space is empty. -/
theorem ext {x y : X} (h : ∀ j, P.stage j x = P.stage j y) : x = y := by
  apply P.equiv.injective
  apply Subtype.ext
  funext j
  exact h j

/-- The canonical presentation using all discrete quotients of a profinite space. -/
noncomputable def ofProfinite (X : Profinite.{u}) :
    FiniteDiscretePresentation X where
  index := DiscreteQuotient X
  diagram := X.fintypeDiagram
  equiv := CompHausLike.homeoOfIso X.isoAsLimitConeLift

/-- In the canonical presentation, the finite-stage coordinate is the quotient projection. -/
@[simp]
theorem ofProfinite_stage_apply (X : Profinite.{u}) (A : DiscreteQuotient X) (x : X) :
    (ofProfinite X).stage A x = A.proj x := by
  rfl

/-- Refinement maps in the canonical presentation are surjective, even for an empty space. -/
theorem ofProfinite_transition_surjective (X : Profinite.{u})
    {A B : DiscreteQuotient X} (h : A ≤ B) :
    Function.Surjective (DiscreteQuotient.ofLE h) := by
  intro b
  obtain ⟨x, rfl⟩ := B.proj_surjective b
  exact ⟨A.proj x, DiscreteQuotient.ofLE_proj h x⟩

end FiniteDiscretePresentation

/-- For a Hausdorff space, a finite-discrete presentation is equivalent to
compactness together with a clopen topological basis.

Corresponds to Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, Lemma
(1.1.1), using Mathlib’s clopen-basis API. -/
theorem finiteDiscretePresentation_iff_compact_clopenBasis (X : Type u)
    [TopologicalSpace X] [T2Space X] :
    Nonempty (FiniteDiscretePresentation X) ↔
      CompactSpace X ∧ IsTopologicalBasis {s : Set X | IsClopen s} := by
  constructor
  · rintro ⟨P⟩
    let : CompactSpace X := Homeomorph.compactSpace P.equiv.symm
    let : TotallyDisconnectedSpace X :=
      Homeomorph.totallyDisconnectedSpace P.equiv.symm
    exact ⟨inferInstance, isTopologicalBasis_isClopen⟩
  · rintro ⟨hcompact, hclopen⟩
    let : CompactSpace X := hcompact
    let : TotallySeparatedSpace X :=
      totallySeparatedSpace_of_t0_of_basis_clopen hclopen
    exact ⟨FiniteDiscretePresentation.ofProfinite (Profinite.of X)⟩

/-- For a Hausdorff space, a finite-discrete presentation is equivalent to
compactness and total disconnectedness. The empty space is included.

This is the finite-discrete characterization in Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Ch. I §1, Lemma (1.1.1), including the empty space. -/
theorem finiteDiscretePresentation_iff_compact_totallyDisconnected (X : Type u)
    [TopologicalSpace X] [T2Space X] :
    Nonempty (FiniteDiscretePresentation X) ↔
      CompactSpace X ∧ TotallyDisconnectedSpace X := by
  constructor
  · rintro ⟨P⟩
    exact ⟨Homeomorph.compactSpace P.equiv.symm,
      Homeomorph.totallyDisconnectedSpace P.equiv.symm⟩
  · rintro ⟨hcompact, hdisconnected⟩
    let : CompactSpace X := hcompact
    let : TotallyDisconnectedSpace X := hdisconnected
    exact ⟨FiniteDiscretePresentation.ofProfinite (Profinite.of X)⟩
