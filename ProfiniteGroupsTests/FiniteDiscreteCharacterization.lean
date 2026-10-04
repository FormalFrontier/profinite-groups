/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteDiscreteCharacterization
public import Mathlib.Topology.Order

/-! # Empty, finite, and infinite discrete-space presentation clients -/

@[expose] public section

set_option warningAsError true

namespace ProfiniteGroupsTests.FiniteDiscreteCharacterization

/-- The empty space admits the canonical finite-discrete presentation. -/
example : Nonempty (FiniteDiscretePresentation PEmpty) :=
  ⟨FiniteDiscretePresentation.ofProfinite (Profinite.of PEmpty)⟩

/-- Finite discrete spaces admit finite-discrete presentations. -/
example : Nonempty (FiniteDiscretePresentation (Fin 2)) :=
  ⟨FiniteDiscretePresentation.ofProfinite (Profinite.of (Fin 2))⟩

/-- The infinite discrete space has a clopen basis but fails the compactness condition. -/
example : TopologicalSpace.IsTopologicalBasis {s : Set ℕ | IsClopen s} ∧
    ¬ CompactSpace ℕ := by
  constructor
  · exact (isTopologicalBasis_singletons ℕ).of_isOpen_of_subset
      (fun _ hs => hs.isOpen) (by
        rintro _ ⟨x, rfl⟩
        exact isClopen_discrete {x})
  · exact not_compactSpace_iff.mpr inferInstance

/-- The characterization applies to the empty Hausdorff space. -/
example : TotallyDisconnectedSpace PEmpty :=
  ((finiteDiscretePresentation_iff_compact_totallyDisconnected PEmpty).mp
    ⟨FiniteDiscretePresentation.ofProfinite (Profinite.of PEmpty)⟩).2

/-- The finite-discrete presentation yields a clopen basis. -/
example : TopologicalSpace.IsTopologicalBasis
    {s : Set (Fin 2) | IsClopen s} :=
  ((finiteDiscretePresentation_iff_compact_clopenBasis (Fin 2)).mp
    ⟨FiniteDiscretePresentation.ofProfinite (Profinite.of (Fin 2))⟩).2

/-- Distinct points in a finite discrete example differ at a finite stage. -/
example (P : FiniteDiscretePresentation (Fin 2)) :
    ∃ j, P.stage j 0 ≠ P.stage j 1 := by
  by_contra h
  have heq : (0 : Fin 2) = 1 := P.ext (fun j => by
    by_contra hj
    exact h ⟨j, hj⟩)
  exact Fin.zero_ne_one heq

/-- A continuous finite-stage map composes with a diagram transition. -/
example (P : FiniteDiscretePresentation (Fin 2)) {j k : P.index}
    (f : j ⟶ k) (x : Fin 2) :
    ((P.topDiagram.map f).hom.comp (P.stageMap j)) x = P.stage k x := by
  simpa only [P.stageMap_apply] using congrArg
    (fun map : C(Fin 2, P.stageSpace k) => map x) (P.stageMap_naturality f)

end ProfiniteGroupsTests.FiniteDiscreteCharacterization
