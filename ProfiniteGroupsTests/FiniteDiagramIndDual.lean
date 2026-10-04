/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteDiagramIndDual
public import ProfiniteGroupsTests.FiniteStageImages

/-!
# Boundary clients for finite-diagram dual ind-objects

Constant two-point and empty diagrams give nonempty and empty finite stages.
The under-category of a one-point finite set has distinct parallel arrows and
a non-surjective tail projection. The class and projection clients use the
ind-dual comparison; the diagrams, arrows and cofilteredness are independent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Profinite
open ProfiniteGroupsTests.FiniteStageImages

set_option warningAsError true

namespace ProfiniteGroupsTests.FiniteDiagramIndDual

private def point : oneIndex := Discrete.mk PUnit.unit

def two : oneIndex ⥤ FintypeCat.Skeleton.{0} :=
  (Functor.const oneIndex).obj (FintypeCat.Skeleton.mk 2)

private def empty : oneIndex ⥤ FintypeCat.Skeleton.{0} :=
  (Functor.const oneIndex).obj (FintypeCat.Skeleton.mk 0)

private def pointed : pointedIndex ⥤ FintypeCat.Skeleton.{0} :=
  Under.forget (FintypeCat.Skeleton.mk 1)

private def swap : FintypeCat.Skeleton.mk 2 ⟶ FintypeCat.Skeleton.mk 2 :=
  fun x => ULift.up (Fin.rev x.down)

private def swapNat : two ⟶ two where
  app _ := swap
  naturality := by
    intro i j a
    cases i with
    | mk i =>
      cases j with
      | mk j =>
        cases i
        cases j
        rfl

private def zero : FintypeCat.Skeleton.mk 2 ⟶ FintypeCat.Skeleton.mk 2 :=
  fun _ => ULift.up (0 : Fin 2)

private def zeroNat : two ⟶ two where
  app _ := zero
  naturality := by
    intro i j a
    cases i with
    | mk i =>
      cases j with
      | mk j =>
        cases i
        cases j
        rfl

/-- The constant two-point presentation carries the swap-induced morphism. -/
private noncomputable def swapInd : finiteDiagramIndDual two ⟶ finiteDiagramIndDual two :=
  finiteDiagramIndDualMap swapNat

/-- Applying the diagram swap twice gives the identity dual ind-morphism. -/
example : swapInd ≫ swapInd = 𝟙 (finiteDiagramIndDual two) := by
  have h : swapNat ≫ swapNat = 𝟙 two := by
    ext j
    funext x
    cases x with
    | up index =>
      change ULift.up (Fin.rev (Fin.rev index)) = ULift.up index
      rw [Fin.rev_rev]
  change finiteDiagramIndDualMap swapNat ≫ finiteDiagramIndDualMap swapNat =
    𝟙 (finiteDiagramIndDual two)
  rw [← finiteDiagramIndDualMap_comp, h, finiteDiagramIndDualMap_id]

/-- Swapping before collapsing differs from collapsing before swapping. -/
example : (swap ≫ zero) (ULift.up (0 : Fin 2)) ≠
    (zero ≫ swap) (ULift.up (0 : Fin 2)) := by
  decide

/-- The swap and identity are distinct already as finite-stage maps. -/
example : swap ≠ (𝟙 (FintypeCat.Skeleton.mk 2)) := by
  intro h
  have hvalue := congrFun h (ULift.up (0 : Fin 2))
  have hfin : Fin.rev (0 : Fin 2) = 0 := congrArg ULift.down hvalue
  exact (by decide : Fin.rev (0 : Fin 2) ≠ 0) hfin

def twoLimit : Cone (((two ⋙ FintypeCat.Skeleton.incl) ⋙
    FintypeCat.toProfinite)) :=
  Profinite.limitCone _

def zeroSection : twoLimit.pt :=
  ⟨fun _ => ULift.up (0 : Fin 2), by intro i j a; rfl⟩

private theorem swapClass_ne_id :
    stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
      ((two ⋙ FintypeCat.Skeleton.incl).obj point) point
      (FintypeCat.Skeleton.incl.map swap) ≠
    stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
      ((two ⋙ FintypeCat.Skeleton.incl).obj point) point (𝟙 _) := by
  intro heq
  obtain ⟨k, a, b, hab⟩ :=
    (stageHomClass_eq_iff (two ⋙ FintypeCat.Skeleton.incl) _
      point point (FintypeCat.Skeleton.incl.map swap) (𝟙 _)).1 heq
  have hk : k = point := by
    cases k with
    | mk k => cases k; rfl
  subst k
  have ha : a = 𝟙 point := Subsingleton.elim _ _
  have hb : b = 𝟙 point := Subsingleton.elim _ _
  subst a
  subst b
  have hmap : FintypeCat.Skeleton.incl.map swap = 𝟙 _ := by
    simpa [two] using hab
  have hswap : swap = 𝟙 _ :=
    FintypeCat.Skeleton.incl.map_injective (by simpa using hmap)
  have hvalue := congrFun hswap (ULift.up (0 : Fin 2))
  have hfin : Fin.rev (0 : Fin 2) = 0 := congrArg ULift.down hvalue
  exact (by decide : Fin.rev (0 : Fin 2) ≠ 0) hfin

private theorem swap_coordinate :
    (finiteDiagramIndDualHomMap two two (finiteDiagramIndDualMap swapNat)).val point =
      stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
        ((two ⋙ FintypeCat.Skeleton.incl).obj point) point
        (FintypeCat.Skeleton.incl.map swap) := by
  have hn := finiteDiagramIndDualHomMap_target_naturality
    two two two swapNat (𝟙 (finiteDiagramIndDual two)) point point
      (𝟙 ((two ⋙ FintypeCat.Skeleton.incl).obj point))
      (finiteDiagramIndDualHomMap_id two point)
  simpa only [Functor.comp_obj, swapNat, Category.id_comp] using hn

private theorem zero_coordinate :
    (finiteDiagramIndDualHomMap two two (finiteDiagramIndDualMap zeroNat)).val point =
      stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
        ((two ⋙ FintypeCat.Skeleton.incl).obj point) point
        (FintypeCat.Skeleton.incl.map zero) := by
  have hn := finiteDiagramIndDualHomMap_target_naturality
    two two two zeroNat (𝟙 (finiteDiagramIndDual two)) point point
      (𝟙 ((two ⋙ FintypeCat.Skeleton.incl).obj point))
      (finiteDiagramIndDualHomMap_id two point)
  simpa only [Functor.comp_obj, zeroNat, Category.id_comp] using hn

/-- The representative of each composite respects its order at the two-point stage. -/
example :
    (finiteDiagramIndDualHomMap two two
      (swapInd ≫ finiteDiagramIndDualMap zeroNat)).val point =
        stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
          ((two ⋙ FintypeCat.Skeleton.incl).obj point) point
          (FintypeCat.Skeleton.incl.map swap ≫ FintypeCat.Skeleton.incl.map zero) ∧
    (finiteDiagramIndDualHomMap two two
      (finiteDiagramIndDualMap zeroNat ≫ swapInd)).val point =
        stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
          ((two ⋙ FintypeCat.Skeleton.incl).obj point) point
          (FintypeCat.Skeleton.incl.map zero ≫ FintypeCat.Skeleton.incl.map swap) := by
  constructor
  · exact finiteDiagramIndDualHomMap_comp_class two two two
      swapInd (finiteDiagramIndDualMap zeroNat) point point point
      (FintypeCat.Skeleton.incl.map swap) (FintypeCat.Skeleton.incl.map zero)
      (by simpa only [swapInd] using swap_coordinate) zero_coordinate
  · exact finiteDiagramIndDualHomMap_comp_class two two two
      (finiteDiagramIndDualMap zeroNat) swapInd point point point
      (FintypeCat.Skeleton.incl.map zero) (FintypeCat.Skeleton.incl.map swap)
      zero_coordinate (by simpa only [swapInd] using swap_coordinate)

/-- The nonidentity source swap acts on the representative before zero collapse. -/
example : (finiteDiagramIndDualHomMap two two
    (finiteDiagramIndDualMap swapNat ≫ finiteDiagramIndDualMap zeroNat)).val point =
      stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
        ((two ⋙ FintypeCat.Skeleton.incl).obj point) point
        (FintypeCat.Skeleton.incl.map swap ≫ FintypeCat.Skeleton.incl.map zero) := by
  exact finiteDiagramIndDualHomMap_source_naturality two two two swapNat
    (finiteDiagramIndDualMap zeroNat) point point
    (FintypeCat.Skeleton.incl.map zero) zero_coordinate

/-- The swap of a constant two-point presentation is not the identity
of its dual ind-object. -/
example : finiteDiagramIndDualMap swapNat ≠
    (𝟙 (finiteDiagramIndDual two)) := by
  intro heq
  have hcoord := congrArg
    (fun g : finiteDiagramIndDual two ⟶ finiteDiagramIndDual two =>
      (finiteDiagramIndDualHomMap two two g).val point) heq
  rw [swap_coordinate, finiteDiagramIndDualHomMap_id] at hcoord
  exact swapClass_ne_id hcoord

/-- The corresponding continuous map swaps the value at the chosen
two-point limit section. -/
example :
    (finiteDiagramIndDualContinuousEquiv two two twoLimit
      (Profinite.limitConeIsLimit _) twoLimit
      (Profinite.limitConeIsLimit _)
      (finiteDiagramIndDualMap swapNat) ≫ twoLimit.π.app point) zeroSection =
      ULift.up (1 : Fin 2) := by
  rw [finiteDiagramIndDualContinuousEquiv_apply_class
    two two twoLimit (Profinite.limitConeIsLimit _)
    twoLimit (Profinite.limitConeIsLimit _)
    (finiteDiagramIndDualMap swapNat) point point
    (FintypeCat.Skeleton.incl.map swap) swap_coordinate]
  change ULift.up (Fin.rev (0 : Fin 2)) = ULift.up (1 : Fin 2)
  decide

/-- The identity coordinate is a genuine class at the two-point stage. -/
example : (finiteDiagramIndDualHomMap two two
    (𝟙 (finiteDiagramIndDual two))).val point =
      stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
        ((two ⋙ FintypeCat.Skeleton.incl).obj point) point (𝟙 _) :=
  finiteDiagramIndDualHomMap_id two point

/-- An empty finite source stage has maps both to an empty target and
to a two-point target. -/
example : Nonempty (finiteDiagramIndDual empty ⟶ finiteDiagramIndDual empty) :=
  ⟨𝟙 _⟩

private noncomputable def emptyToTwoSections :
    ((two ⋙ FintypeCat.Skeleton.incl) ⋙
      stageHomFunctor (empty ⋙ FintypeCat.Skeleton.incl)).sections :=
  ⟨fun _ => stageHomClass (empty ⋙ FintypeCat.Skeleton.incl)
    ((two ⋙ FintypeCat.Skeleton.incl).obj point) point
      (FintypeCat.homMk (fun x => Fin.elim0 x.down)), by
    intro i j a
    cases i with
    | mk i =>
      cases j with
      | mk j =>
        cases i
        cases j
        have ha : a = 𝟙 _ := Subsingleton.elim _ _
        subst a
        exact (((two ⋙ FintypeCat.Skeleton.incl) ⋙
          stageHomFunctor (empty ⋙ FintypeCat.Skeleton.incl)).map_id_apply
            (Discrete.mk PUnit.unit) _)⟩

example : Nonempty (finiteDiagramIndDual empty ⟶ finiteDiagramIndDual two) :=
  ⟨(finiteDiagramIndDualHomEquiv empty two).symm emptyToTwoSections⟩

/-- An empty finite source has a continuous map to the two-point limit. -/
example : Nonempty ((Profinite.limitCone
      (((empty ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))).pt ⟶
    twoLimit.pt) :=
  ⟨finiteDiagramIndDualContinuousEquiv empty two (Profinite.limitCone _)
    (Profinite.limitConeIsLimit _) twoLimit (Profinite.limitConeIsLimit _)
      ((finiteDiagramIndDualHomEquiv empty two).symm emptyToTwoSections)⟩

/-- The empty-stage representative determines the projection of the
continuous map to the two-point target. -/
example :
    finiteDiagramIndDualContinuousEquiv empty two (Profinite.limitCone _)
      (Profinite.limitConeIsLimit _) twoLimit (Profinite.limitConeIsLimit _)
      ((finiteDiagramIndDualHomEquiv empty two).symm emptyToTwoSections) ≫
      twoLimit.π.app point =
    (Profinite.limitCone (((empty ⋙ FintypeCat.Skeleton.incl) ⋙
      FintypeCat.toProfinite))).π.app point ≫
      FintypeCat.toProfinite.map (FintypeCat.homMk (fun x => Fin.elim0 x.down)) := by
  apply finiteDiagramIndDualContinuousEquiv_apply_class empty two
    (Profinite.limitCone _) (Profinite.limitConeIsLimit _)
    twoLimit (Profinite.limitConeIsLimit _)
    ((finiteDiagramIndDualHomEquiv empty two).symm emptyToTwoSections)
    point point (FintypeCat.homMk (fun x => Fin.elim0 x.down))
  exact finiteDiagramIndDualHomEquiv_symm_apply_class empty two
    emptyToTwoSections point point _ rfl

/-- There is no map from a two-point finite stage to an empty one. -/
example : IsEmpty (finiteDiagramIndDual two ⟶ finiteDiagramIndDual empty) := by
  constructor
  intro f
  have h := (finiteDiagramIndDualHomMap two empty f).val point
  obtain ⟨i, g, _⟩ := Limits.Types.jointly_surjective' h
  cases i with
  | op i =>
    change (two ⋙ FintypeCat.Skeleton.incl).obj i ⟶
      (empty ⋙ FintypeCat.Skeleton.incl).obj point at g
    exact Fin.elim0 (g (ULift.up (0 : Fin 2))).down

/-- The pointed-set presentation uses a genuine nonposetal cofiltered index. -/
noncomputable example : finiteDiagramIndDual pointed ⟶ finiteDiagramIndDual pointed := 𝟙 _

/-- Both parallel target arrows constrain the same tail coordinate. -/
example :
    stageHomPost (F := pointed ⋙ FintypeCat.Skeleton.incl)
      (FintypeCat.Skeleton.incl.map (pointed.map identityArrow))
      ((finiteDiagramIndDualHomMap pointed pointed
        (𝟙 (finiteDiagramIndDual pointed))).val tailStage) =
      (finiteDiagramIndDualHomMap pointed pointed
        (𝟙 (finiteDiagramIndDual pointed))).val tailStage ∧
    stageHomPost (F := pointed ⋙ FintypeCat.Skeleton.incl)
      (FintypeCat.Skeleton.incl.map (pointed.map collapseArrow))
      ((finiteDiagramIndDualHomMap pointed pointed
        (𝟙 (finiteDiagramIndDual pointed))).val tailStage) =
      (finiteDiagramIndDualHomMap pointed pointed
        (𝟙 (finiteDiagramIndDual pointed))).val tailStage :=
  ⟨finiteDiagramIndDualHomMap_target_arrow pointed pointed _ identityArrow,
    finiteDiagramIndDualHomMap_target_arrow pointed pointed _ collapseArrow⟩

/-- The distinct tail representatives agree after refinement at the singleton. -/
private theorem tailClasses_eq :
    stageHomClass (pointed ⋙ FintypeCat.Skeleton.incl)
      ((pointed ⋙ FintypeCat.Skeleton.incl).obj tailStage) tailStage (𝟙 _) =
    stageHomClass (pointed ⋙ FintypeCat.Skeleton.incl)
      ((pointed ⋙ FintypeCat.Skeleton.incl).obj tailStage) tailStage
        ((pointed ⋙ FintypeCat.Skeleton.incl).map collapseArrow) := by
  apply (stageHomClass_eq_iff (pointed ⋙ FintypeCat.Skeleton.incl) _
    tailStage tailStage _ _).2
  refine ⟨singletonStage, singletonToTail, singletonToTail, ?_⟩
  ext x
  rfl

/-- The tail identity and collapsing parallel arrow are genuinely different
stage maps, even though their colimit classes agree. -/
example : (𝟙 ((pointed ⋙ FintypeCat.Skeleton.incl).obj tailStage)) ≠
    (pointed ⋙ FintypeCat.Skeleton.incl).map collapseArrow := by
  intro h
  have hvalue := congrArg (fun g : (pointed ⋙ FintypeCat.Skeleton.incl).obj tailStage ⟶
    (pointed ⋙ FintypeCat.Skeleton.incl).obj tailStage => g (ULift.up (1 : Fin 2))) h
  have heq : (1 : Fin 2) = 0 := congrArg ULift.down hvalue
  exact (by decide : (1 : Fin 2) ≠ 0) heq

/-- The identity coordinate can equally be represented by the collapsing
parallel arrow, without cancelling a non-surjective limit projection. -/
example : (finiteDiagramIndDualHomMap pointed pointed
    (𝟙 (finiteDiagramIndDual pointed))).val tailStage =
    stageHomClass (pointed ⋙ FintypeCat.Skeleton.incl)
      ((pointed ⋙ FintypeCat.Skeleton.incl).obj tailStage) tailStage
      ((pointed ⋙ FintypeCat.Skeleton.incl).map collapseArrow) :=
  (finiteDiagramIndDualHomMap_id pointed tailStage).trans tailClasses_eq

example : ¬ Function.Surjective
    (pointedLimit.π.app tailStage : pointedLimit.pt → pointedDiagram.obj tailStage) :=
  tail_projection_not_surjective

/-- The same refined class computes the continuous identity's projection
through a tail representative that differs from the tail identity. -/
example :
    finiteDiagramIndDualContinuousEquiv pointed pointed pointedLimit
      (Profinite.limitConeIsLimit _) pointedLimit
      (Profinite.limitConeIsLimit _) (𝟙 (finiteDiagramIndDual pointed)) ≫
      pointedLimit.π.app tailStage =
    pointedLimit.π.app tailStage ≫
      FintypeCat.toProfinite.map
        ((pointed ⋙ FintypeCat.Skeleton.incl).map collapseArrow) := by
  apply finiteDiagramIndDualContinuousEquiv_apply_class
    pointed pointed pointedLimit (Profinite.limitConeIsLimit _)
    pointedLimit (Profinite.limitConeIsLimit _)
    (𝟙 (finiteDiagramIndDual pointed)) tailStage tailStage
    ((pointed ⋙ FintypeCat.Skeleton.incl).map collapseArrow)
  exact (finiteDiagramIndDualHomMap_id pointed tailStage).trans tailClasses_eq

end ProfiniteGroupsTests.FiniteDiagramIndDual
