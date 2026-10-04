/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteDiagramHomLimit
public import ProfiniteGroupsTests.FiniteTargetHomColimit
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Clients for the outer finite-diagram hom comparison

A one-arrow target sees both coordinates of a nonconstant map. Empty target
diagrams and empty source stages test the absence of extra inhabitance
conditions. A pointed-set source tests refinement without cancelling its
non-surjective projection.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Profinite
open ProfiniteGroupsTests.FiniteStageImages

set_option warningAsError true

namespace ProfiniteGroupsTests.FiniteDiagramHomLimit

private def point : oneIndex := Discrete.mk PUnit.unit

/-- The limiting constant two-point source cone for the one-arrow client. -/
def sourceCone : Cone (nonemptyDiagram ⋙ FintypeCat.toProfinite) :=
  Profinite.limitCone _

private def sourceIsLimit : IsLimit sourceCone := Profinite.limitConeIsLimit _

private def twoToThree : nonemptyDiagram.obj point ⟶ FintypeCat.of (Fin 3) :=
  FintypeCat.homMk (fun (value : Fin 2) => if value = 0 then 2 else 1)

/-- The one-arrow finite target diagram from three points to two. -/
abbrev arrowDiagram : Fin 2 ⥤ FintypeCat.{0} :=
  ComposableArrows.mk₁ FiniteTargetHomColimit.threeToTwo

/-- The limiting cone of the one-arrow target. -/
def arrowTarget : Cone (arrowDiagram ⋙ FintypeCat.toProfinite) :=
  Profinite.limitCone _

private def arrowIsLimit : IsLimit arrowTarget := Profinite.limitConeIsLimit _

private def arrowCone : Cone (arrowDiagram ⋙ FintypeCat.toProfinite) where
  pt := sourceCone.pt
  π :=
    { app
        | 0 => sourceCone.π.app point ≫ FintypeCat.toProfinite.map twoToThree
        | 1 => sourceCone.π.app point ≫
            FintypeCat.toProfinite.map
              (twoToThree ≫ FiniteTargetHomColimit.threeToTwo)
      naturality := by
        intro j k arrow
        fin_cases j <;> fin_cases k
        · have : arrow = 𝟙 (0 : Fin 2) := Subsingleton.elim _ _
          subst arrow
          simp
        · have : arrow = homOfLE (show (0 : Fin 2) ≤ 1 by decide) :=
            Subsingleton.elim _ _
          subst arrow
          change (sourceCone.π.app point ≫ FintypeCat.toProfinite.map twoToThree) ≫
            FintypeCat.toProfinite.map FiniteTargetHomColimit.threeToTwo =
              sourceCone.π.app point ≫ FintypeCat.toProfinite.map
                (twoToThree ≫ FiniteTargetHomColimit.threeToTwo)
          simp only [FintypeCat.toProfinite.map_comp, Category.assoc]
        · exact (show ¬ (1 : Fin 2) ≤ 0 by decide) (leOfHom arrow) |>.elim
        · have : arrow = 𝟙 (1 : Fin 2) := Subsingleton.elim _ _
          subst arrow
          simp }

private def arrowMap : sourceCone.pt ⟶ arrowTarget.pt :=
  arrowIsLimit.lift arrowCone

private def zeroSection : sourceCone.pt :=
  ⟨fun _ => (0 : Fin 2), by intro i j arrow; rfl⟩

private def oneSection : sourceCone.pt :=
  ⟨fun _ => (1 : Fin 2), by intro i j arrow; rfl⟩

/-- The zero coordinate of the forward map retains a nonconstant finite-stage map. -/
private theorem arrowClass_zero :
    (stageHomLimitMap nonemptyDiagram sourceCone sourceIsLimit
      arrowDiagram arrowTarget arrowMap).val 0 =
      stageHomClass nonemptyDiagram (FintypeCat.of (Fin 3)) point twoToThree := by
  change (stageHomLimitMap nonemptyDiagram sourceCone sourceIsLimit
    arrowDiagram arrowTarget arrowMap).val 0 =
      stageHomClass nonemptyDiagram (arrowDiagram.obj 0) point
        (show nonemptyDiagram.obj point ⟶ arrowDiagram.obj 0 from twoToThree)
  apply (stageHomEquiv sourceCone sourceIsLimit (arrowDiagram.obj 0)).injective
  rw [stageHomLimitMap_apply, Equiv.apply_symm_apply, stageHomEquiv_apply_class]
  exact arrowIsLimit.fac arrowCone 0

/-- The second target coordinate is the postcomposition of the first one. -/
private theorem arrowClass_one :
    (stageHomLimitMap nonemptyDiagram sourceCone sourceIsLimit
      arrowDiagram arrowTarget arrowMap).val 1 =
      stageHomClass nonemptyDiagram (FintypeCat.of (Fin 2)) point
        (twoToThree ≫ FiniteTargetHomColimit.threeToTwo) := by
  change (stageHomLimitMap nonemptyDiagram sourceCone sourceIsLimit
    arrowDiagram arrowTarget arrowMap).val 1 =
      stageHomClass nonemptyDiagram (arrowDiagram.obj 1) point
        (show nonemptyDiagram.obj point ⟶ arrowDiagram.obj 1 from
          twoToThree ≫ FiniteTargetHomColimit.threeToTwo)
  apply (stageHomEquiv sourceCone sourceIsLimit (arrowDiagram.obj 1)).injective
  rw [stageHomLimitMap_apply, Equiv.apply_symm_apply, stageHomEquiv_apply_class]
  exact arrowIsLimit.fac arrowCone 1

/-- The target arrow sends the first class to the second by postcomposition. -/
example :
    (stageHomLimitMap nonemptyDiagram sourceCone sourceIsLimit
      arrowDiagram arrowTarget arrowMap).val 1 =
    stageHomPost (F := nonemptyDiagram) FiniteTargetHomColimit.threeToTwo
      ((stageHomLimitMap nonemptyDiagram sourceCone sourceIsLimit
        arrowDiagram arrowTarget arrowMap).val 0) := by
  rw [arrowClass_one, arrowClass_zero, stageHomPost_class]

/-- The first coordinate takes different values at the two source-limit points. -/
example :
    stageHomToContinuous sourceCone (FintypeCat.of (Fin 3))
      ((stageHomLimitEquiv nonemptyDiagram sourceCone
        sourceIsLimit arrowDiagram arrowTarget
        arrowIsLimit arrowMap).val 0) zeroSection = (2 : Fin 3) ∧
    stageHomToContinuous sourceCone (FintypeCat.of (Fin 3))
      ((stageHomLimitEquiv nonemptyDiagram sourceCone
        sourceIsLimit arrowDiagram arrowTarget
        arrowIsLimit arrowMap).val 0) oneSection = (1 : Fin 3) := by
  constructor
  · rw [stageHomLimitEquiv_apply, arrowClass_zero, stageHomToContinuous_class]
    rfl
  · rw [stageHomLimitEquiv_apply, arrowClass_zero, stageHomToContinuous_class]
    rfl

/-- The second coordinate changes both of those values after target postcomposition. -/
example :
    stageHomToContinuous sourceCone (FintypeCat.of (Fin 2))
      ((stageHomLimitEquiv nonemptyDiagram sourceCone
        sourceIsLimit arrowDiagram arrowTarget
        arrowIsLimit arrowMap).val 1) zeroSection = (1 : Fin 2) ∧
    stageHomToContinuous sourceCone (FintypeCat.of (Fin 2))
      ((stageHomLimitEquiv nonemptyDiagram sourceCone
        sourceIsLimit arrowDiagram arrowTarget
        arrowIsLimit arrowMap).val 1) oneSection = (0 : Fin 2) := by
  constructor
  · rw [stageHomLimitEquiv_apply, arrowClass_one, stageHomToContinuous_class]
    rfl
  · rw [stageHomLimitEquiv_apply, arrowClass_one, stageHomToContinuous_class]
    rfl

private abbrev noTargetIndex : Type := Discrete PEmpty

private def noTarget : noTargetIndex ⥤ FintypeCat.{0} :=
  (Functor.const noTargetIndex).obj (FintypeCat.of (Fin 2))

private def noTargetCone : Cone (noTarget ⋙ FintypeCat.toProfinite) :=
  Profinite.limitCone _

private def noTargetIsLimit : IsLimit noTargetCone := Profinite.limitConeIsLimit _

private def noTargetSection (F : oneIndex ⥤ FintypeCat.{0}) :
    (noTarget ⋙ stageHomFunctor F).sections :=
  ⟨(fun j => nomatch j), by
    intro j
    cases j with
    | mk impossible => exact impossible.elim⟩

/-- With no target objects there is precisely one compatible family. -/
private theorem noTargetSection_unique (F : oneIndex ⥤ FintypeCat.{0})
    (x : (noTarget ⋙ stageHomFunctor F).sections) : x = noTargetSection F := by
  apply Subtype.ext
  funext j
  cases j with
  | mk impossible => exact impossible.elim

/-- The empty target limit is terminal, independently of the source point. -/
private theorem noTargetLimit_unique (F : oneIndex ⥤ FintypeCat.{0})
    (c : Cone (F ⋙ FintypeCat.toProfinite)) (hc : IsLimit c) :
    ∃! f : c.pt ⟶ noTargetCone.pt,
      stageHomLimitEquiv F c hc noTarget noTargetCone
        noTargetIsLimit f = noTargetSection F := by
  let emptyCone : Cone (noTarget ⋙ FintypeCat.toProfinite) :=
    { pt := c.pt
      π := { app := fun j => nomatch j
             naturality := by
               intro j
               cases j with
               | mk impossible => exact impossible.elim } }
  refine ⟨noTargetIsLimit.lift emptyCone, ?_, ?_⟩
  · exact noTargetSection_unique F _
  · intro other _
    apply noTargetIsLimit.hom_ext
    intro j
    cases j with
    | mk impossible => exact impossible.elim

/-- Even from an empty source limit there is exactly one empty family. -/
example :
    ∃! f : (Profinite.limitCone
      (emptyDiagram ⋙ FintypeCat.toProfinite)).pt ⟶ noTargetCone.pt,
      stageHomLimitEquiv emptyDiagram (Profinite.limitCone _)
        (Profinite.limitConeIsLimit _) noTarget noTargetCone
          noTargetIsLimit f = noTargetSection emptyDiagram :=
  noTargetLimit_unique emptyDiagram _ _

/-- The same terminal comparison also applies to a nonempty source limit. -/
example :
    ∃! f : sourceCone.pt ⟶ noTargetCone.pt,
      stageHomLimitEquiv nonemptyDiagram sourceCone
        sourceIsLimit noTarget noTargetCone
          noTargetIsLimit f = noTargetSection nonemptyDiagram :=
  noTargetLimit_unique nonemptyDiagram sourceCone sourceIsLimit

/-- There is no source point for the constant empty-stage diagram. -/
example : IsEmpty (Profinite.limitCone
    (emptyDiagram ⋙ FintypeCat.toProfinite)).pt :=
  ⟨fun value => Fin.elim0
    ((Profinite.limitCone (emptyDiagram ⋙ FintypeCat.toProfinite)).π.app point value)⟩

/-- An empty source limit still has a map to the empty finite target. -/
private def emptyToEmpty : emptyDiagram.obj point ⟶ FintypeCat.of (Fin 0) :=
  FintypeCat.homMk Fin.elim0

private def emptyToTwo : emptyDiagram.obj point ⟶ FintypeCat.of (Fin 2) :=
  FintypeCat.homMk Fin.elim0

private noncomputable def emptySourceSection (S : FintypeCat.{0})
    (g : emptyDiagram.obj point ⟶ S) :
    ((Functor.const oneIndex).obj S ⋙ stageHomFunctor emptyDiagram).sections :=
  ⟨fun _ => stageHomClass emptyDiagram S point g, by
    intro j k arrow
    cases j with
    | mk j =>
      cases k with
      | mk k =>
        cases arrow
        change ((stageHomFunctor emptyDiagram).map (𝟙 S))
          (stageHomClass emptyDiagram S point g) = _
        exact (stageHomFunctor emptyDiagram).map_id_apply S _⟩

/-- The zero-point source has a compatible component for the empty target. -/
example :
    let G := (Functor.const oneIndex).obj (FintypeCat.of (Fin 0))
    let d := Profinite.limitCone (G ⋙ FintypeCat.toProfinite)
    let x := emptySourceSection (FintypeCat.of (Fin 0)) emptyToEmpty
    (stageHomLimitEquiv emptyDiagram (Profinite.limitCone _)
      (Profinite.limitConeIsLimit _) G d (Profinite.limitConeIsLimit _)).symm x ≫
        d.π.app point =
      (Profinite.limitCone (emptyDiagram ⋙ FintypeCat.toProfinite)).π.app point ≫
        FintypeCat.toProfinite.map emptyToEmpty := by
  dsimp only
  apply stageHomLimitEquiv_symm_apply_class
  rfl

/-- The zero-point source likewise has a component for a two-point target. -/
example :
    let G := (Functor.const oneIndex).obj (FintypeCat.of (Fin 2))
    let d := Profinite.limitCone (G ⋙ FintypeCat.toProfinite)
    let x := emptySourceSection (FintypeCat.of (Fin 2)) emptyToTwo
    (stageHomLimitEquiv emptyDiagram (Profinite.limitCone _)
      (Profinite.limitConeIsLimit _) G d (Profinite.limitConeIsLimit _)).symm x ≫
        d.π.app point =
      (Profinite.limitCone (emptyDiagram ⋙ FintypeCat.toProfinite)).π.app point ≫
        FintypeCat.toProfinite.map emptyToTwo := by
  dsimp only
  apply stageHomLimitEquiv_symm_apply_class
  rfl

private def tailMap : pointedDiagram.obj tailStage ⟶ FintypeCat.of Bool :=
  FintypeCat.homMk tailFunction

private def pointedIsLimit : IsLimit pointedLimit := Profinite.limitConeIsLimit _

private def constantMap : pointedDiagram.obj tailStage ⟶ FintypeCat.of Bool :=
  FintypeCat.homMk constantFunction

private noncomputable def pointedSection
    (g : pointedDiagram.obj tailStage ⟶ FintypeCat.of Bool) :
    ((Functor.const oneIndex).obj (FintypeCat.of Bool) ⋙
      stageHomFunctor pointedDiagram).sections :=
  ⟨fun _ => stageHomClass pointedDiagram (FintypeCat.of Bool) tailStage g, by
    intro j k arrow
    cases j with
    | mk j =>
      cases k with
      | mk k =>
        cases arrow
        change ((stageHomFunctor pointedDiagram).map (𝟙 (FintypeCat.of Bool)))
          (stageHomClass pointedDiagram (FintypeCat.of Bool) tailStage g) = _
        exact (stageHomFunctor pointedDiagram).map_id_apply (FintypeCat.of Bool) _⟩

private theorem pointedSection_eq : pointedSection tailMap = pointedSection constantMap := by
  apply Subtype.ext
  funext j
  apply (stageHomClass_eq_iff pointedDiagram (FintypeCat.of Bool)
    tailStage tailStage tailMap constantMap).2
  refine ⟨singletonStage, singletonToTail, singletonToTail, ?_⟩
  ext value
  rfl

/-- Different stage maps can determine the same inverse target projection,
because the source limit does not surject onto the chosen stage. -/
example :
    let G := (Functor.const oneIndex).obj (FintypeCat.of Bool)
    let d := Profinite.limitCone (G ⋙ FintypeCat.toProfinite)
    ((stageHomLimitEquiv pointedDiagram pointedLimit
      pointedIsLimit G d (Profinite.limitConeIsLimit _)).symm
        (pointedSection tailMap)) ≫ d.π.app point =
    ((stageHomLimitEquiv pointedDiagram pointedLimit
      pointedIsLimit G d (Profinite.limitConeIsLimit _)).symm
        (pointedSection constantMap)) ≫ d.π.app point := by
  dsimp only
  rw [stageHomLimitEquiv_symm_apply_projection,
    stageHomLimitEquiv_symm_apply_projection, pointedSection_eq]

/-- The source stage maps above really differ away from the image of the
limit projection; their equality is not obtained by cancellation. -/
example : tailMap ≠ constantMap ∧
    ¬ Function.Surjective
      (pointedLimit.π.app tailStage : pointedLimit.pt → pointedDiagram.obj tailStage) := by
  constructor
  · intro h
    have hvalue := congrArg
      (fun g : pointedDiagram.obj tailStage ⟶ FintypeCat.of Bool =>
        g (ULift.up (1 : Fin 2))) h
    change tailFunction (ULift.up (1 : Fin 2)) =
      constantFunction (ULift.up (1 : Fin 2)) at hvalue
    exact (by simp [tailFunction, constantFunction] :
      tailFunction (ULift.up (1 : Fin 2)) ≠
        constantFunction (ULift.up (1 : Fin 2))) hvalue
  · exact tail_projection_not_surjective

end ProfiniteGroupsTests.FiniteDiagramHomLimit
