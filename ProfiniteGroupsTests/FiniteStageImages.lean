/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteStageImages
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Boundary clients for finite-stage image stabilization

Constant finite diagrams include both inhabited and empty limits. The
under-category of a one-point finite set is a small cofiltered category
with parallel arrows: its forgetful diagram has a one-point initial stage
and a two-point later stage, whose limit projection is not surjective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat

set_option warningAsError true

namespace ProfiniteGroupsTests.FiniteStageImages

/-- The one-object index for constant finite diagrams. -/
abbrev oneIndex : Type := Discrete.{0} PUnit

/-- The constant two-point diagram. -/
def nonemptyDiagram : oneIndex ⥤ FintypeCat.{0} :=
  (Functor.const oneIndex).obj (FintypeCat.of (Fin 2))

/-- The constant empty diagram. -/
def emptyDiagram : oneIndex ⥤ FintypeCat.{0} :=
  (Functor.const oneIndex).obj (FintypeCat.of (Fin 0))

/-- A constant nonempty finite diagram has an inhabited limiting cone. -/
example : Nonempty (Profinite.limitCone
    (nonemptyDiagram ⋙ FintypeCat.toProfinite)).pt := by
  refine ⟨⟨fun _ => (0 : Fin 2), ?_⟩⟩
  intro i j a
  rfl

/-- The image theorem applies to a constant two-point limit. -/
example : ∃ (j : oneIndex) (a : j ⟶ Discrete.mk PUnit.unit),
    Set.range ((Profinite.limitCone
        (nonemptyDiagram ⋙ FintypeCat.toProfinite)).π.app (Discrete.mk PUnit.unit) :
        _ → nonemptyDiagram.obj (Discrete.mk PUnit.unit)) =
      Set.range (nonemptyDiagram.map a : nonemptyDiagram.obj j →
        nonemptyDiagram.obj (Discrete.mk PUnit.unit)) :=
  Profinite.exists_stage_range_eq
    (Profinite.limitCone (nonemptyDiagram ⋙ FintypeCat.toProfinite))
    (Profinite.limitConeIsLimit (nonemptyDiagram ⋙ FintypeCat.toProfinite))
    (Discrete.mk PUnit.unit)

/-- A constant empty finite diagram has an empty limiting cone. -/
example : IsEmpty (Profinite.limitCone (emptyDiagram ⋙ FintypeCat.toProfinite)).pt :=
  ⟨fun x => Fin.elim0
    ((Profinite.limitCone (emptyDiagram ⋙ FintypeCat.toProfinite)).π.app
      (Discrete.mk PUnit.unit) x)⟩

/-- The eventual-emptiness conclusion applies without a nonempty-stage hypothesis. -/
example : ∃ j : oneIndex, IsEmpty (emptyDiagram.obj j) := by
  have hEmpty : IsEmpty (Profinite.limitCone (emptyDiagram ⋙ FintypeCat.toProfinite)).pt :=
    ⟨fun x => Fin.elim0
      ((Profinite.limitCone (emptyDiagram ⋙ FintypeCat.toProfinite)).π.app
        (Discrete.mk PUnit.unit) x)⟩
  exact @Profinite.exists_isEmpty_stage_of_isEmpty_limit
    oneIndex _ _ emptyDiagram (Profinite.limitCone _)
    (Profinite.limitConeIsLimit _) hEmpty

/-- Finite pointed sets, presented as objects under a singleton skeleton object. -/
abbrev pointedIndex : Type :=
  Under (FintypeCat.Skeleton.mk 1 : FintypeCat.Skeleton.{0})

instance : IsCofiltered pointedIndex :=
  IsCofiltered.of_isInitial pointedIndex Under.mkIdInitial

/-- Forget the distinguished point of a finite pointed set. -/
def pointedDiagram : pointedIndex ⥤ FintypeCat.{0} :=
  Under.forget (FintypeCat.Skeleton.mk 1) ⋙ FintypeCat.Skeleton.incl

/-- A two-point stage with distinguished point zero. -/
def tailStage : pointedIndex :=
  Under.mk (fun _ : ULift (Fin 1) => ULift.up (0 : Fin 2))

/-- The singleton initial stage of the pointed-set index. -/
def singletonStage : pointedIndex :=
  Under.mk (𝟙 (FintypeCat.Skeleton.mk 1))

/-- The singleton-stage transition lands at the distinguished point. -/
def singletonToTail : singletonStage ⟶ tailStage :=
  Under.homMk (fun _ : ULift (Fin 1) => ULift.up (0 : Fin 2)) (by rfl)

/-- The identity arrow at the two-point stage. -/
def identityArrow : tailStage ⟶ tailStage :=
  Under.homMk (𝟙 tailStage.right)

/-- The nonidentity endomorphism collapsing the two points to zero. -/
def collapseArrow : tailStage ⟶ tailStage :=
  Under.homMk (fun _ : ULift (Fin 2) => ULift.up (0 : Fin 2))
    (by
      funext x
      obtain ⟨value⟩ := x
      fin_cases value
      rfl)

/-- The index has genuinely distinct parallel arrows at a nonempty stage. -/
example : identityArrow ≠ collapseArrow := by
  intro h
  have h' := congrArg (fun a : tailStage ⟶ tailStage =>
    a.right (ULift.up (1 : Fin 2))) h
  have hvalue : ULift.up (1 : Fin 2) = ULift.up (0 : Fin 2) := by
    change ULift.up (1 : Fin 2) = ULift.up (0 : Fin 2) at h'
    exact h'
  have heq : (1 : Fin 2) = 0 := congrArg ULift.down hvalue
  exact (by decide : (1 : Fin 2) ≠ 0) heq

/-- Cofilteredness equalizes the two parallel arrows. -/
example : ∃ (j : pointedIndex) (a : j ⟶ tailStage),
    a ≫ identityArrow = a ≫ collapseArrow := by
  exact ⟨IsCofiltered.eq identityArrow collapseArrow,
    IsCofiltered.eqHom identityArrow collapseArrow,
    IsCofiltered.eq_condition identityArrow collapseArrow⟩

/-- The explicit limiting cone of the finite pointed-set diagram. -/
def pointedLimit :=
  Profinite.limitCone (pointedDiagram ⋙ FintypeCat.toProfinite)

private theorem tail_projection_eq_zero (x : pointedLimit.pt) :
    (pointedLimit.π.app tailStage x : ULift (Fin 2)) = ULift.up (0 : Fin 2) := by
  have h := congrArg
    (fun a : pointedLimit.pt ⟶ FintypeCat.toProfinite.obj (pointedDiagram.obj tailStage) => a x)
    (pointedLimit.w collapseArrow)
  change (ULift.up (0 : Fin 2) : ULift (Fin 2)) = pointedLimit.π.app tailStage x at h
  exact h.symm

/-- The singleton initial stage gives a point of the limit. -/
example : Nonempty pointedLimit.pt := by
  let c := (FintypeCat.Skeleton.incl ⋙ FintypeCat.toProfinite).mapCone
    (Under.forgetCone (FintypeCat.Skeleton.mk 1 : FintypeCat.Skeleton.{0}))
  exact ⟨(Profinite.limitConeIsLimit _).lift c (ULift.up (0 : Fin 1))⟩

/-- The two-point tail projection of this non-posetal diagram is not surjective. -/
theorem tail_projection_not_surjective : ¬ Function.Surjective
    (pointedLimit.π.app tailStage : pointedLimit.pt → pointedDiagram.obj tailStage) := by
  intro h
  obtain ⟨x, hx⟩ := h (ULift.up (1 : Fin 2))
  have heq := tail_projection_eq_zero x
  rw [hx] at heq
  exact (by decide : (1 : Fin 2) ≠ 0) (congrArg ULift.down heq)

/-- Distinguish the designated point in the two-point stage. -/
def tailFunction (x : pointedDiagram.obj tailStage) : Bool :=
  (x : ULift (Fin 2)).down == (0 : Fin 2)

/-- A constant function which agrees with `tailFunction` on the limit. -/
def constantFunction (_ : pointedDiagram.obj tailStage) : Bool := true

/-- Two functions differ on the tail stage outside the limit image. -/
example : tailFunction (ULift.up (1 : Fin 2)) ≠
    constantFunction (ULift.up (1 : Fin 2)) := by
  simp [tailFunction, constantFunction]

/-- The singleton-stage transition makes the two functions agree. -/
example : ∀ x : pointedDiagram.obj singletonStage,
    tailFunction (pointedDiagram.map singletonToTail x) =
      constantFunction (pointedDiagram.map singletonToTail x) := by
  intro x
  rfl

/-- Despite that difference, they agree on the limit and hence after refinement. -/
example : ∃ (j : pointedIndex) (a : j ⟶ tailStage),
    ∀ x : pointedDiagram.obj j,
      tailFunction (pointedDiagram.map a x) = constantFunction (pointedDiagram.map a x) := by
  exact Profinite.exists_stage_map_eq_of_limit_eq pointedLimit
    (Profinite.limitConeIsLimit _) tailStage tailFunction constantFunction
    (fun x => by simp [tailFunction, constantFunction, tail_projection_eq_zero x])

/-- Comparison with a function from the one-point stage has the same
common-refinement form, with no identification of the two source stages. -/
example : ∃ (j : pointedIndex) (a : j ⟶ tailStage) (b : j ⟶ singletonStage),
    ∀ x : pointedDiagram.obj j,
      tailFunction (pointedDiagram.map a x) =
        (fun _ : pointedDiagram.obj singletonStage => true) (pointedDiagram.map b x) := by
  obtain ⟨j, a, b, h⟩ :=
    Profinite.exists_common_stage_map_eq_of_limit_eq pointedLimit
      (Profinite.limitConeIsLimit _) tailStage singletonStage
      tailFunction (fun _ => true)
      (fun x => by simp [tailFunction, tail_projection_eq_zero x])
  exact ⟨j, a, b, h⟩

end ProfiniteGroupsTests.FiniteStageImages
