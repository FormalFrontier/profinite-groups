/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteDiscreteCharacterization
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Finite-group presentations of topological groups

A presentation records a topological group equivalence to the explicit limit
of a small cofiltered diagram of finite groups. In particular its topology is
the inverse-limit topology. The canonical presentation uses open normal
quotients.

The index and finite groups live in the universe of the carrier, as does
Mathlib's canonical open-normal-quotient diagram. Open subgroups are also
closed; the neighborhood-basis condition records openness and normality.
-/

@[expose] public section

open CategoryTheory Filter
open scoped Topology

universe u

namespace OpenNormalSubgroup

/-- The whole group supplies an object of the cofiltered category of open normal subgroups. -/
instance instNonempty (G : Type u) [Group G] [TopologicalSpace G] :
    Nonempty (OpenNormalSubgroup G) :=
  ⟨{ toSubgroup := ⊤, isOpen' := isOpen_univ }⟩

end OpenNormalSubgroup

/-- A presentation of a topological group as a cofiltered limit of finite groups. -/
structure FiniteGroupPresentation (G : Type u) [Group G] [TopologicalSpace G] where
  index : Type u
  [smallCategory : SmallCategory index]
  [cofiltered : IsCofiltered index]
  diagram : index ⥤ FiniteGrp.{u}
  equiv : G ≃ₜ* (ProfiniteGrp.limitCone
    (diagram ⋙ forget₂ FiniteGrp ProfiniteGrp)).pt

attribute [instance] FiniteGroupPresentation.smallCategory FiniteGroupPresentation.cofiltered

namespace FiniteGroupPresentation

variable {G : Type u} [Group G] [TopologicalSpace G]
    (P : FiniteGroupPresentation G)

/-- The presentation diagram, viewed as a diagram of profinite groups. -/
abbrev groupDiagram : P.index ⥤ ProfiniteGrp.{u} :=
  P.diagram ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The finite discrete group at an index of the presentation. -/
abbrev stageGroup (j : P.index) : ProfiniteGrp.{u} :=
  P.groupDiagram.obj j

/-- The composite of the group-limit equivalence with a finite-stage projection. -/
def stage (j : P.index) : G → P.stageGroup j :=
  letI : SmallCategory P.index := P.smallCategory
  fun g => (ProfiniteGrp.limitCone (P.diagram ⋙ forget₂ FiniteGrp ProfiniteGrp)).π.app j
    (P.equiv g)

@[simp]
theorem stage_apply (j : P.index) (g : G) :
    P.stage j g =
      (ProfiniteGrp.limitCone P.groupDiagram).π.app j (P.equiv g) := rfl

/-- Group-limit coordinates are continuous for the inverse-limit topology. -/
theorem continuous_stage (j : P.index) : Continuous (P.stage j) := by
  exact (((ProfiniteGrp.limitCone (P.diagram ⋙
    forget₂ FiniteGrp ProfiniteGrp)).π.app j).hom.continuous_toFun).comp
      P.equiv.continuous_toFun

/-- The stage projection sends the identity to the identity. -/
theorem stage_one (j : P.index) : P.stage j 1 = 1 := by
  rw [P.stage_apply]
  simp

/-- Group-limit coordinates respect multiplication. -/
theorem stage_mul (j : P.index) (g h : G) :
    P.stage j (g * h) = P.stage j g * P.stage j h := by
  simp only [P.stage_apply, map_mul]

/-- The continuous group homomorphism from a presentation to a finite-stage group. -/
def stageHom (j : P.index) : G →ₜ* P.stageGroup j where
  toFun := P.stage j
  map_one' := P.stage_one j
  map_mul' := P.stage_mul j
  continuous_toFun := P.continuous_stage j

@[simp]
theorem stageHom_apply (j : P.index) (g : G) : P.stageHom j g = P.stage j g := rfl

@[simp]
theorem stageHom_toMonoidHom_apply (j : P.index) (g : G) :
    (P.stageHom j).toMonoidHom g = P.stage j g := rfl

/-- Group-limit coordinates commute with the transition homomorphisms. -/
@[simp]
theorem stage_naturality {j k : P.index} (f : j ⟶ k) (g : G) :
    (P.groupDiagram.map f) (P.stage j g) = P.stage k g := by
  exact (P.equiv g).2 f

/-- The continuous homomorphisms to finite stages respect transitions. -/
theorem stageHom_naturality {j k : P.index} (f : j ⟶ k) :
    (P.groupDiagram.map f).hom.comp (P.stageHom j) = P.stageHom k := by
  ext g
  exact P.stage_naturality f g

/-- Finite-stage coordinates separate elements of the group. -/
theorem ext {g h : G} (heq : ∀ j, P.stage j g = P.stage j h) : g = h := by
  apply P.equiv.injective
  apply Subtype.ext
  funext j
  exact heq j

/-- The canonical presentation via quotients by open normal subgroups. -/
noncomputable def ofProfiniteGrp (G : ProfiniteGrp.{u}) :
    FiniteGroupPresentation G where
  index := OpenNormalSubgroup G
  diagram := G.toFiniteQuotientFunctor
  equiv := G.continuousMulEquivLimittoFiniteQuotientFunctor

/-- In the canonical presentation, the finite-group coordinate is the quotient projection. -/
@[simp]
theorem ofProfiniteGrp_stage_apply (G : ProfiniteGrp.{u}) (U : OpenNormalSubgroup G)
    (g : G) : (ofProfiniteGrp G).stage U g = QuotientGroup.mk g := by
  rfl

/-- The canonical continuous finite-quotient projection is surjective. -/
theorem ofProfiniteGrp_stageHom_surjective (G : ProfiniteGrp.{u})
    (U : OpenNormalSubgroup G) :
    Function.Surjective ((ofProfiniteGrp G).stageHom U) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup q
  exact ⟨g, (stageHom_apply (ofProfiniteGrp G) U g).trans
    (ofProfiniteGrp_stage_apply G U g)⟩

end FiniteGroupPresentation

/-- For a Hausdorff topological group, a finite-group presentation is equivalent
to compactness and an identity-neighborhood basis of open normal subgroups. -/
theorem finiteGroupPresentation_iff_compact_openNormalBasis (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] :
    Nonempty (FiniteGroupPresentation G) ↔
      CompactSpace G ∧
        ∀ U : Set G, U ∈ 𝓝 (1 : G) →
          ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ U := by
  constructor
  · rintro ⟨P⟩
    let : CompactSpace G := Homeomorph.compactSpace P.equiv.symm.toHomeomorph
    let : TotallyDisconnectedSpace G :=
      Homeomorph.totallyDisconnectedSpace P.equiv.symm.toHomeomorph
    refine ⟨inferInstance, ?_⟩
    intro U hU
    obtain ⟨V, hVU, hVopen, hVone⟩ := mem_nhds_iff.mp hU
    obtain ⟨H, hH⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVopen hVone
    exact ⟨H, hH.trans hVU⟩
  · rintro ⟨hcompact, hbasis⟩
    let : CompactSpace G := hcompact
    have hdisconnected : TotallyDisconnectedSpace G := by
      apply totallyDisconnectedSpace_iff_connectedComponent_one.mpr
      apply Set.Subset.antisymm
      · intro g hg
        by_contra hne
        have hU : ({g}ᶜ : Set G) ∈ 𝓝 (1 : G) :=
          isOpen_compl_singleton.mem_nhds (by
            have hne' : g ≠ (1 : G) := by simpa only [Set.mem_singleton_iff] using hne
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hne'.symm)
        obtain ⟨H, hH⟩ := hbasis _ hU
        have hgH := (H.isClopen.connectedComponent_subset H.one_mem) hg
        exact (hH hgH) (by simp)
      · intro g hg
        change g = 1 at hg
        subst g
        exact mem_connectedComponent
    let : TotallyDisconnectedSpace G := hdisconnected
    exact ⟨FiniteGroupPresentation.ofProfiniteGrp (ProfiniteGrp.of G)⟩

/-- For a Hausdorff topological group, a finite-group presentation is equivalent
to compactness and total disconnectedness. This includes the trivial group. -/
theorem finiteGroupPresentation_iff_compact_totallyDisconnected (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] :
    Nonempty (FiniteGroupPresentation G) ↔
      CompactSpace G ∧ TotallyDisconnectedSpace G := by
  constructor
  · rintro ⟨P⟩
    exact ⟨Homeomorph.compactSpace P.equiv.symm.toHomeomorph,
      Homeomorph.totallyDisconnectedSpace P.equiv.symm.toHomeomorph⟩
  · rintro ⟨hcompact, hdisconnected⟩
    let : CompactSpace G := hcompact
    let : TotallyDisconnectedSpace G := hdisconnected
    exact ⟨FiniteGroupPresentation.ofProfiniteGrp (ProfiniteGrp.of G)⟩
