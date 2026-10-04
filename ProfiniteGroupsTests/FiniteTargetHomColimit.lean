/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteTargetHomColimit
public import ProfiniteGroupsTests.FiniteStageImages

/-!
# Boundary clients for finite-target stage maps

The constant diagrams include nonconstant maps and empty-stage maps to
both empty and inhabited targets. The pointed-set index includes distinct
parallel arrows and a projection that is not surjective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Profinite
open ProfiniteGroupsTests.FiniteStageImages

set_option warningAsError true

namespace ProfiniteGroupsTests.FiniteTargetHomColimit

private def point : oneIndex := Discrete.mk PUnit.unit

/-- A nonconstant map from the constant two-point stage to three points. -/
private def twoToThree : nonemptyDiagram.obj point ⟶ FintypeCat.of (Fin 3) :=
  FintypeCat.homMk (fun (x : Fin 2) => if x = 0 then 2 else 1)

/-- Postcomposition changes both values of `twoToThree`. -/
def threeToTwo : FintypeCat.of (Fin 3) ⟶ FintypeCat.of (Fin 2) :=
  FintypeCat.homMk (fun x => if x = 2 then 1 else 0)

private def zeroSection :
    (Profinite.limitCone (nonemptyDiagram ⋙ FintypeCat.toProfinite)).pt :=
  ⟨fun _ => (0 : Fin 2), by intro i j a; rfl⟩

private def oneSection :
    (Profinite.limitCone (nonemptyDiagram ⋙ FintypeCat.toProfinite)).pt :=
  ⟨fun _ => (1 : Fin 2), by intro i j a; rfl⟩

/-- The representative yields a nonconstant continuous map on the limit. -/
example :
    Profinite.stageHomToContinuous
      (Profinite.limitCone (nonemptyDiagram ⋙ FintypeCat.toProfinite))
      (FintypeCat.of (Fin 3))
      (stageHomClass nonemptyDiagram (FintypeCat.of (Fin 3)) point twoToThree)
        zeroSection ≠
    Profinite.stageHomToContinuous
      (Profinite.limitCone (nonemptyDiagram ⋙ FintypeCat.toProfinite))
      (FintypeCat.of (Fin 3))
      (stageHomClass nonemptyDiagram (FintypeCat.of (Fin 3)) point twoToThree)
        oneSection := by
  rw [stageHomToContinuous_class]
  change (2 : Fin 3) ≠ 1
  decide

/-- The component of the natural comparison evaluates a nonconstant
representative at a point of the constant limit. -/
example :
    let comparison : (Profinite.limitCone
        (nonemptyDiagram ⋙ FintypeCat.toProfinite)).pt ⟶
        FintypeCat.toProfinite.obj (FintypeCat.of (Fin 3)) :=
      (stageHomNatIso (Profinite.limitCone _)
        (Profinite.limitConeIsLimit _)).hom.app (FintypeCat.of (Fin 3))
          (stageHomClass nonemptyDiagram (FintypeCat.of (Fin 3)) point twoToThree)
    comparison zeroSection = (2 : Fin 3) := by
  dsimp only
  rw [stageHomNatIso_hom_app_apply_class]
  change (2 : Fin 3) = 2
  rfl

/-- Target postcomposition is visible at the same point of the limit. -/
example :
    Profinite.stageHomToContinuous
      (Profinite.limitCone (nonemptyDiagram ⋙ FintypeCat.toProfinite))
      (FintypeCat.of (Fin 2))
      (stageHomPost (F := nonemptyDiagram) threeToTwo
        (stageHomClass nonemptyDiagram (FintypeCat.of (Fin 3)) point twoToThree))
      zeroSection = (1 : Fin 2) := by
  rw [Profinite.stageHomToContinuous_naturality, stageHomToContinuous_class]
  change (1 : Fin 2) = 1
  rfl

/-- The empty-stage diagram has representatives even for the empty target. -/
private def emptyToEmpty : FintypeCat.of (Fin 0) ⟶ FintypeCat.of (Fin 0) :=
  FintypeCat.homMk Fin.elim0

private def emptyToTwo : FintypeCat.of (Fin 0) ⟶ FintypeCat.of (Fin 2) :=
  FintypeCat.homMk Fin.elim0

example : Nonempty (colimit (stageHom emptyDiagram (FintypeCat.of (Fin 0)))) :=
  ⟨stageHomClass emptyDiagram (FintypeCat.of (Fin 0)) point emptyToEmpty⟩

/-- The empty-stage diagram also has representatives for an inhabited target. -/
example : Nonempty (colimit (stageHom emptyDiagram (FintypeCat.of (Fin 2)))) :=
  ⟨stageHomClass emptyDiagram (FintypeCat.of (Fin 2)) point emptyToTwo⟩

private abbrev noIndex : Type := Discrete PEmpty

private def noStages : noIndex ⥤ FintypeCat.{0} :=
  (Functor.const noIndex).obj (FintypeCat.of PUnit)

/-- With no indices, the colimit of stage maps is empty. -/
example : IsEmpty (colimit (noStages.op ⋙ yoneda.obj (FintypeCat.of PUnit))) := by
  constructor
  intro x
  obtain ⟨i, _, _⟩ := Limits.Types.jointly_surjective' x
  cases i.unop with
  | mk impossible => exact impossible.elim

/-- With no indices, the limit still contains a point. -/
example : Nonempty (Profinite.limitCone (noStages ⋙ FintypeCat.toProfinite)).pt := by
  refine ⟨⟨fun i => ?_, ?_⟩⟩
  · cases i with
    | mk impossible => exact impossible.elim
  · intro i j a
    cases i with
    | mk impossible => exact impossible.elim

/-- The comparison computes the map from an empty limit to an empty target. -/
example :
    (stageHomEquiv (Profinite.limitCone _)
      (Profinite.limitConeIsLimit _) (FintypeCat.of (Fin 0)))
        (stageHomClass emptyDiagram (FintypeCat.of (Fin 0)) point emptyToEmpty) =
      (Profinite.limitCone (emptyDiagram ⋙ FintypeCat.toProfinite)).π.app point ≫
        FintypeCat.toProfinite.map emptyToEmpty := by
  exact stageHomEquiv_apply_class _ _ _ _ _

private def tailMap : pointedDiagram.obj tailStage ⟶ FintypeCat.of Bool :=
  FintypeCat.homMk tailFunction

private def constantMap : pointedDiagram.obj tailStage ⟶ FintypeCat.of Bool :=
  FintypeCat.homMk constantFunction

/-- The two maps differ away from the image of the limit projection. -/
example : tailMap ≠ constantMap := by
  intro h
  have hvalue := congrArg
    (fun g : pointedDiagram.obj tailStage ⟶ FintypeCat.of Bool =>
      g (ULift.up (1 : Fin 2))) h
  change tailFunction (ULift.up (1 : Fin 2)) =
    constantFunction (ULift.up (1 : Fin 2)) at hvalue
  exact (show tailFunction (ULift.up (1 : Fin 2)) ≠
    constantFunction (ULift.up (1 : Fin 2)) from by
      simp [tailFunction, constantFunction]) hvalue

/-- Distinct maps from a non-surjectively projected stage represent the
same map from the limit, as witnessed by the singleton-stage refinement. -/
private theorem tailClass_eq :
    stageHomClass pointedDiagram (FintypeCat.of Bool) tailStage tailMap =
    stageHomClass pointedDiagram (FintypeCat.of Bool) tailStage constantMap := by
  apply (stageHomClass_eq_iff pointedDiagram (FintypeCat.of Bool) tailStage tailStage
    tailMap constantMap).2
  refine ⟨singletonStage, singletonToTail, singletonToTail, ?_⟩
  ext x
  rfl

/-- The same two classes give equal continuous maps without cancelling the
non-surjective projection. -/
example :
    Profinite.stageHomToContinuous pointedLimit (FintypeCat.of Bool)
      (stageHomClass pointedDiagram (FintypeCat.of Bool) tailStage tailMap) =
    Profinite.stageHomToContinuous pointedLimit (FintypeCat.of Bool)
      (stageHomClass pointedDiagram (FintypeCat.of Bool) tailStage constantMap) := by
  exact congrArg (Profinite.stageHomToContinuous pointedLimit (FintypeCat.of Bool))
    tailClass_eq

/-- Inversion of the comparison finds the same refined class for two
different stage maps. -/
example :
    (stageHomEquiv pointedLimit (Profinite.limitConeIsLimit _)
      (FintypeCat.of Bool)).symm
        (pointedLimit.π.app tailStage ≫ FintypeCat.toProfinite.map tailMap) =
      stageHomClass pointedDiagram (FintypeCat.of Bool) tailStage constantMap := by
  exact (stageHomEquiv_symm_apply_projection pointedLimit
    (Profinite.limitConeIsLimit _) (FintypeCat.of Bool) tailStage tailMap).trans
      tailClass_eq

end ProfiniteGroupsTests.FiniteTargetHomColimit
