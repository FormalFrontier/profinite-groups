/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteGroupCharacterization
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.Int

/-! # Trivial and nontrivial finite-group presentation clients -/

@[expose] public section

set_option warningAsError true

namespace ProfiniteGroupsTests.FiniteGroupCharacterization

open Filter
open scoped Topology

/-- The trivial group has a canonical open-normal-quotient presentation. -/
example : Nonempty (FiniteGroupPresentation PUnit) :=
  ⟨FiniteGroupPresentation.ofProfiniteGrp
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))⟩

/-- Finite nontrivial groups also have open-normal-quotient presentations. -/
example : Nonempty (FiniteGroupPresentation (ProfiniteGrp.ofFiniteGrp
    (FiniteGrp.of (Multiplicative (ZMod 2))))) :=
  ⟨FiniteGroupPresentation.ofProfiniteGrp _⟩

/-- The normal-basis criterion applies to the trivial group. -/
example : ∀ U : Set PUnit, U ∈ 𝓝 (1 : PUnit) →
    ∃ H : OpenNormalSubgroup PUnit, (H : Set PUnit) ⊆ U :=
  ((finiteGroupPresentation_iff_compact_openNormalBasis PUnit).mp
    ⟨FiniteGroupPresentation.ofProfiniteGrp
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))⟩).2

/-- The presentation criterion yields total disconnectedness for a nontrivial finite group. -/
example : TotallyDisconnectedSpace (ProfiniteGrp.ofFiniteGrp
    (FiniteGrp.of (Multiplicative (ZMod 2)))) :=
  ((finiteGroupPresentation_iff_compact_totallyDisconnected
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 2))))).mp
    ⟨FiniteGroupPresentation.ofProfiniteGrp _⟩).2

/-- The infinite discrete group has an open-normal basis but is not compact. -/
example :
    (∀ U : Set (Multiplicative ℤ), U ∈ 𝓝 (1 : Multiplicative ℤ) →
      ∃ H : OpenNormalSubgroup (Multiplicative ℤ), (H : Set (Multiplicative ℤ)) ⊆ U) ∧
      ¬ CompactSpace (Multiplicative ℤ) := by
  constructor
  · intro U hU
    let H : OpenNormalSubgroup (Multiplicative ℤ) :=
      { toSubgroup := ⊥, isOpen' := isOpen_discrete _ }
    refine ⟨H, ?_⟩
    intro x hx
    have hx1 : x = 1 := by
      change x ∈ (⊥ : Subgroup (Multiplicative ℤ)) at hx
      simpa using hx
    exact hx1 ▸ mem_of_mem_nhds hU
  · exact not_compactSpace_iff.mpr inferInstance

/-- The nontrivial finite group has distinguishable finite-stage coordinates. -/
example (P : FiniteGroupPresentation (ProfiniteGrp.ofFiniteGrp
    (FiniteGrp.of (Multiplicative (ZMod 2))))) :
    ∃ j, P.stage j (Multiplicative.ofAdd (0 : ZMod 2)) ≠
      P.stage j (Multiplicative.ofAdd (1 : ZMod 2)) := by
  by_contra h
  have heq := P.ext (fun j => by
    by_contra hj
    exact h ⟨j, hj⟩)
  exact (show (Multiplicative.ofAdd (0 : ZMod 2)) ≠
    Multiplicative.ofAdd (1 : ZMod 2) by decide) heq

/-- Bundled projections compose with the transition homomorphisms. -/
example (P : FiniteGroupPresentation (ProfiniteGrp.ofFiniteGrp
    (FiniteGrp.of (Multiplicative (ZMod 2))))) {j k : P.index}
    (f : j ⟶ k) (g : ProfiniteGrp.ofFiniteGrp
      (FiniteGrp.of (Multiplicative (ZMod 2)))) :
    ((P.groupDiagram.map f).hom.comp (P.stageHom j)) g = P.stage k g := by
  simpa only [P.stageHom_apply] using congrArg
    (fun hom : _ →ₜ* P.stageGroup k => hom g) (P.stageHom_naturality f)

/-- The bundled projection kernel detects trivial finite-quotient classes. -/
example (G : ProfiniteGrp) (U : OpenNormalSubgroup G) (g : G) :
    g ∈ ((FiniteGroupPresentation.ofProfiniteGrp G).stageHom U).toMonoidHom.ker ↔
      (QuotientGroup.mk g : G ⧸ U.toSubgroup) = 1 := by
  have projection :
      ((FiniteGroupPresentation.ofProfiniteGrp G).stageHom U).toMonoidHom g =
        (QuotientGroup.mk g : G ⧸ U.toSubgroup) :=
    (FiniteGroupPresentation.stageHom_toMonoidHom_apply
      (FiniteGroupPresentation.ofProfiniteGrp G) U g).trans
      (FiniteGroupPresentation.ofProfiniteGrp_stage_apply G U g)
  constructor
  · intro hg
    exact projection.symm.trans (MonoidHom.mem_ker.mp hg)
  · intro hg
    exact MonoidHom.mem_ker.mpr (projection.trans hg)

end ProfiniteGroupsTests.FiniteGroupCharacterization
