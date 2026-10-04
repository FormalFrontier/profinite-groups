/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.IndDualRealization
public import ProfiniteGroupsTests.FiniteDiagramIndDual

/-!
# Boundary clients for realization of dual ind-objects

Nonidentity and noncommuting maps are visible already in the finite stages.
A diagram with empty finite stages realizes to an empty space. Two diagrams
with different finite stages present the same dual ind-object through their
common initial stage; their limiting spaces are compared through realization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Profinite Opposite
open ProfiniteGroupsTests.FiniteStageImages
open ProfiniteGroupsTests.FiniteDiagramIndDual (two twoLimit zeroSection)

set_option warningAsError true

namespace ProfiniteGroupsTests.IndDualRealization

private def swap : FintypeCat.Skeleton.mk 2 ⟶ FintypeCat.Skeleton.mk 2 :=
  fun x => ULift.up (Fin.rev x.down)

private def collapse : FintypeCat.Skeleton.mk 2 ⟶ FintypeCat.Skeleton.mk 2 :=
  fun _ => ULift.up (0 : Fin 2)

private def swapNat : two ⟶ two :=
  (Functor.const oneIndex).map swap

private def collapseNat : two ⟶ two :=
  (Functor.const oneIndex).map collapse

/-- The finite data of the two endomorphisms do not commute. -/
example : (swap ≫ collapse) (ULift.up (0 : Fin 2)) ≠
    (collapse ≫ swap) (ULift.up (0 : Fin 2)) := by
  decide

/-- The swap acts nontrivially at a point of a specified finite limit. -/
private theorem continuousSwap_zero :
    (finiteDiagramIndDualContinuousEquiv two two twoLimit
      (Profinite.limitConeIsLimit _) twoLimit (Profinite.limitConeIsLimit _)
      (finiteDiagramIndDualMap swapNat) ≫ twoLimit.π.app (Discrete.mk PUnit.unit))
      zeroSection = ULift.up (1 : Fin 2) := by
  have hcoord := finiteDiagramIndDualHomMap_target_naturality
    two two two swapNat (𝟙 (finiteDiagramIndDual two))
    (Discrete.mk PUnit.unit) (Discrete.mk PUnit.unit)
    (𝟙 ((two ⋙ FintypeCat.Skeleton.incl).obj (Discrete.mk PUnit.unit)))
    (finiteDiagramIndDualHomMap_id two (Discrete.mk PUnit.unit))
  have hclass : (finiteDiagramIndDualHomMap two two
      (finiteDiagramIndDualMap swapNat)).val (Discrete.mk PUnit.unit) =
      stageHomClass (two ⋙ FintypeCat.Skeleton.incl) _ (Discrete.mk PUnit.unit)
        (FintypeCat.Skeleton.incl.map swap) := by
    simpa [swapNat, two] using hcoord
  rw [finiteDiagramIndDualContinuousEquiv_apply_class
    two two twoLimit (Profinite.limitConeIsLimit _)
    twoLimit (Profinite.limitConeIsLimit _)
    (finiteDiagramIndDualMap swapNat) (Discrete.mk PUnit.unit)
    (Discrete.mk PUnit.unit) (FintypeCat.Skeleton.incl.map swap) hclass]
  change ULift.up (Fin.rev (0 : Fin 2)) = ULift.up (1 : Fin 2)
  decide

private def point : oneIndex := Discrete.mk PUnit.unit

/-- Compatible two-point swap classes for a specified finite limit, independently
of a dual ind-object morphism. -/
private noncomputable def swapSections :
    ((two ⋙ FintypeCat.Skeleton.incl) ⋙
      stageHomFunctor (two ⋙ FintypeCat.Skeleton.incl)).sections :=
  ⟨fun _ => stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
      ((two ⋙ FintypeCat.Skeleton.incl).obj point) point
      (FintypeCat.Skeleton.incl.map swap), by
    intro i j arrow
    cases i with
    | mk i =>
      cases j with
      | mk j =>
        cases i
        cases j
        have h : arrow = 𝟙 (Discrete.mk PUnit.unit) := Subsingleton.elim _ _
        subst arrow
        simp only [Functor.comp_obj, Discrete.functor_map_id]
        exact ConcreteCategory.id_apply _⟩

/-- The continuous swap obtained from the specified cone's stage classes. -/
private noncomputable def continuousTwoPointSwap : twoLimit.pt ⟶ twoLimit.pt :=
  (stageHomLimitEquiv (two ⋙ FintypeCat.Skeleton.incl) twoLimit
    (Profinite.limitConeIsLimit _) (two ⋙ FintypeCat.Skeleton.incl) twoLimit
    (Profinite.limitConeIsLimit _)).symm swapSections

private theorem swap_stage_class :
    (finiteDiagramIndDualHomMap two two
      (finiteDiagramIndDualMap swapNat)).val point =
        stageHomClass (two ⋙ FintypeCat.Skeleton.incl)
          ((two ⋙ FintypeCat.Skeleton.incl).obj point) point
          (FintypeCat.Skeleton.incl.map swap) := by
  have hcoord := finiteDiagramIndDualHomMap_target_naturality
    two two two swapNat (𝟙 (finiteDiagramIndDual two)) point point
    (𝟙 ((two ⋙ FintypeCat.Skeleton.incl).obj point))
    (finiteDiagramIndDualHomMap_id two point)
  simpa [swapNat, two] using hcoord

private theorem continuousTwoPointSwap_projection :
    continuousTwoPointSwap ≫ twoLimit.π.app point =
      stageHomToContinuous twoLimit ((two ⋙ FintypeCat.Skeleton.incl).obj point)
        (swapSections.val point) := by
  exact stageHomLimitEquiv_symm_apply_projection
    (two ⋙ FintypeCat.Skeleton.incl) twoLimit (Profinite.limitConeIsLimit _)
    (two ⋙ FintypeCat.Skeleton.incl) twoLimit (Profinite.limitConeIsLimit _)
    swapSections point

private theorem continuousTwoPointSwap_zero :
    (continuousTwoPointSwap ≫ twoLimit.π.app point) zeroSection =
      ULift.up (1 : Fin 2) := by
  rw [continuousTwoPointSwap_projection]
  simp only [swapSections, stageHomToContinuous_class]
  change ULift.up (Fin.rev (0 : Fin 2)) = ULift.up (1 : Fin 2)
  decide

private theorem continuousTwoPointSwap_eq_finite :
    continuousTwoPointSwap =
      finiteDiagramIndDualContinuousEquiv two two twoLimit
        (Profinite.limitConeIsLimit _) twoLimit (Profinite.limitConeIsLimit _)
        (finiteDiagramIndDualMap swapNat) := by
  have hsections : swapSections =
      finiteDiagramIndDualHomMap two two (finiteDiagramIndDualMap swapNat) := by
    apply (Functor.sections_ext_iff).2
    intro j
    have hj : j = point := by
      cases j with
      | mk j => cases j; rfl
    subst j
    simpa only [swapSections] using swap_stage_class.symm
  calc
    _ = (stageHomLimitEquiv (two ⋙ FintypeCat.Skeleton.incl) twoLimit
          (Profinite.limitConeIsLimit _) (two ⋙ FintypeCat.Skeleton.incl) twoLimit
          (Profinite.limitConeIsLimit _)).symm
            (finiteDiagramIndDualHomMap two two (finiteDiagramIndDualMap swapNat)) :=
      congrArg (fun sections =>
        (stageHomLimitEquiv (two ⋙ FintypeCat.Skeleton.incl) twoLimit
          (Profinite.limitConeIsLimit _) (two ⋙ FintypeCat.Skeleton.incl) twoLimit
          (Profinite.limitConeIsLimit _)).symm sections) hsections
    _ = _ := (finiteDiagramIndDualContinuousEquiv_apply two two twoLimit
      (Profinite.limitConeIsLimit _) twoLimit (Profinite.limitConeIsLimit _)
      (finiteDiagramIndDualMap swapNat)).symm

private theorem continuousTwoPointSwap_ne_id : continuousTwoPointSwap ≠ 𝟙 _ := by
  intro h
  have hvalue := congrArg (fun g : twoLimit.pt ⟶ twoLimit.pt =>
    (g ≫ twoLimit.π.app point) zeroSection) h
  rw [continuousTwoPointSwap_zero] at hvalue
  have hfin : (1 : Fin 2) = 0 := congrArg ULift.down hvalue
  exact (by decide : (1 : Fin 2) ≠ 0) hfin

private noncomputable def realizedTwoPointSwap :
    indDualRealization.obj (finiteDiagramIndDual two) ⟶
      indDualRealization.obj (finiteDiagramIndDual two) :=
  let comparison := indDualRealizationComparison two twoLimit
    (Profinite.limitConeIsLimit _)
  comparison.hom ≫ continuousTwoPointSwap ≫ comparison.inv

private theorem realizedTwoPointSwap_ne_id : realizedTwoPointSwap ≠ 𝟙 _ := by
  intro h
  let comparison := indDualRealizationComparison two twoLimit
    (Profinite.limitConeIsLimit _)
  have h' := congrArg (fun g : indDualRealization.obj (finiteDiagramIndDual two) ⟶
    indDualRealization.obj (finiteDiagramIndDual two) =>
      g ≫ comparison.hom) h
  have heq : comparison.hom ≫ continuousTwoPointSwap = comparison.hom := by
    change (comparison.hom ≫ continuousTwoPointSwap ≫ comparison.inv) ≫
      comparison.hom = 𝟙 _ ≫ comparison.hom at h'
    simpa only [Category.assoc, comparison.inv_hom_id,
      Category.comp_id, Category.id_comp] using h'
  have hswap : continuousTwoPointSwap = 𝟙 _ :=
    (cancel_epi comparison.hom).1 (by simpa only [Category.comp_id] using heq)
  exact continuousTwoPointSwap_ne_id hswap

/-- The independently specified swap has the finite-stage-induced morphism as
its preimage; equality is checked at every chosen presentation coordinate. -/
example : (indDualRealizationHomEquiv (finiteDiagramIndDual two)
      (finiteDiagramIndDual two)).symm realizedTwoPointSwap =
    finiteDiagramIndDualMap swapNat := by
  let comparison := indDualRealizationComparison two twoLimit
    (Profinite.limitConeIsLimit _)
  have hnat := indDualRealizationComparison_naturality two two twoLimit
    (Profinite.limitConeIsLimit _) twoLimit (Profinite.limitConeIsLimit _)
    (finiteDiagramIndDualMap swapNat)
  have hrealized : realizedTwoPointSwap =
      indDualRealization.map (finiteDiagramIndDualMap swapNat) := by
    change comparison.hom ≫ continuousTwoPointSwap ≫ comparison.inv = _
    calc
      _ = comparison.hom ≫
          finiteDiagramIndDualContinuousEquiv two two twoLimit
            (Profinite.limitConeIsLimit _) twoLimit (Profinite.limitConeIsLimit _)
            (finiteDiagramIndDualMap swapNat) ≫ comparison.inv :=
        congrArg (fun g : twoLimit.pt ⟶ twoLimit.pt =>
          comparison.hom ≫ g ≫ comparison.inv) continuousTwoPointSwap_eq_finite
      _ = (indDualRealization.map (finiteDiagramIndDualMap swapNat) ≫
          comparison.hom) ≫ comparison.inv := by
        simpa only [Category.assoc] using
          congrArg (· ≫ comparison.inv) hnat.symm
      _ = _ := by
        simp only [Category.assoc, comparison.hom_inv_id, Category.comp_id]
  apply indDualRealization_map_ext
  intro j
  have hmaps : indDualRealization.map
        ((indDualRealizationHomEquiv (finiteDiagramIndDual two)
          (finiteDiagramIndDual two)).symm realizedTwoPointSwap) =
      indDualRealization.map (finiteDiagramIndDualMap swapNat) := by
    calc
      _ = realizedTwoPointSwap := by
        simpa only [indDualRealizationHomEquiv_apply] using
          (indDualRealizationHomEquiv (finiteDiagramIndDual two)
            (finiteDiagramIndDual two)).apply_symm_apply realizedTwoPointSwap
      _ = _ := hrealized
  exact congrArg (· ≫
    (indDualPresentationCone (finiteDiagramIndDual two)).π.app j) hmaps

/-- An independently specified nonidentity continuous map has a nonidentity
ind-object preimage, and the equivalence recovers it coordinatewise. -/
example : ∃ f : finiteDiagramIndDual two ⟶ finiteDiagramIndDual two,
    f ≠ 𝟙 _ ∧ indDualRealization.map f = realizedTwoPointSwap ∧
      ∀ j : (finiteDiagramIndDual two).unop.presentation.Iᵒᵖ,
        (indDualRealization.map f ≫
          (indDualPresentationCone (finiteDiagramIndDual two)).π.app j) =
        (realizedTwoPointSwap ≫
          (indDualPresentationCone (finiteDiagramIndDual two)).π.app j) := by
  let f := (indDualRealizationHomEquiv (finiteDiagramIndDual two)
    (finiteDiagramIndDual two)).symm realizedTwoPointSwap
  refine ⟨f, ?_, ?_, ?_⟩
  · intro hf
    apply realizedTwoPointSwap_ne_id
    have hmap := (indDualRealizationHomEquiv (finiteDiagramIndDual two)
      (finiteDiagramIndDual two)).apply_symm_apply realizedTwoPointSwap
    change (indDualRealizationHomEquiv (finiteDiagramIndDual two)
      (finiteDiagramIndDual two)).symm realizedTwoPointSwap = 𝟙 _ at hf
    rw [indDualRealizationHomEquiv_apply, hf, indDualRealization.map_id] at hmap
    exact hmap.symm
  · exact (indDualRealizationHomEquiv (finiteDiagramIndDual two)
      (finiteDiagramIndDual two)).apply_symm_apply realizedTwoPointSwap
  · intro j
    exact indDualRealizationHomEquiv_symm_apply_comp_π
      (finiteDiagramIndDual two) (finiteDiagramIndDual two) realizedTwoPointSwap j

/-- A nonidentity finite-set map stays nonidentity under realization. -/
example : indDualRealization.map (finiteDiagramIndDualMap swapNat) ≠
    𝟙 (indDualRealization.obj (finiteDiagramIndDual two)) := by
  intro h
  let comparison := indDualRealizationComparison two twoLimit
    (Profinite.limitConeIsLimit _)
  have hnat := indDualRealizationComparison_naturality two two twoLimit
    (Profinite.limitConeIsLimit _) twoLimit (Profinite.limitConeIsLimit _)
    (finiteDiagramIndDualMap swapNat)
  have hcont : finiteDiagramIndDualContinuousEquiv two two twoLimit
      (Profinite.limitConeIsLimit _) twoLimit (Profinite.limitConeIsLimit _)
      (finiteDiagramIndDualMap swapNat) = 𝟙 twoLimit.pt := by
    apply (cancel_epi comparison.hom).1
    simpa only [comparison, h, Category.id_comp, Category.comp_id] using hnat.symm
  have hvalue := congrArg (fun g : twoLimit.pt ⟶ twoLimit.pt =>
    (g ≫ twoLimit.π.app (Discrete.mk PUnit.unit)) zeroSection) hcont
  rw [continuousSwap_zero] at hvalue
  have hvalue' : (1 : Fin 2) = 0 := congrArg ULift.down hvalue
  exact (by decide : (1 : Fin 2) ≠ 0) hvalue'

private def empty : oneIndex ⥤ FintypeCat.Skeleton.{0} :=
  (Functor.const oneIndex).obj (FintypeCat.Skeleton.mk 0)

/-- Realization handles an empty space without inhabited-stage assumptions. -/
example : IsEmpty (indDualRealization.obj (finiteDiagramIndDual empty)) := by
  constructor
  intro x
  let c := Profinite.limitCone ((empty ⋙ FintypeCat.Skeleton.incl) ⋙
    FintypeCat.toProfinite)
  have y : c.pt := (indDualRealizationComparison empty c
    (Profinite.limitConeIsLimit _)).hom x
  exact Fin.elim0 ((c.π.app (Discrete.mk PUnit.unit) y).down)

/-- The pointed-set diagram has both a singleton and a two-point stage. -/
def varied : pointedIndex ⥤ FintypeCat.Skeleton.{0} :=
  Under.forget (FintypeCat.Skeleton.mk 1)

/-- All stages of this second diagram are singletons, unlike `varied`. -/
def singleton : pointedIndex ⥤ FintypeCat.Skeleton.{0} :=
  (Functor.const pointedIndex).obj (FintypeCat.Skeleton.mk 1)

/-- Their diagrams really differ at the two-point stage. -/
theorem varied_ne_singleton_tail : varied.obj tailStage ≠ singleton.obj tailStage := by
  intro h
  have hlen : (2 : ℕ) = 1 := congrArg FintypeCat.Skeleton.len h
  exact (by decide : (2 : ℕ) ≠ 1) hlen

/-- The initial stage of a cofiltered diagram represents its ind-colimit
after reversing the index. -/
private noncomputable def atInitialIso
    (X : pointedIndex ⥤ FintypeCat.Skeleton.{0}) :
    finiteDiagramIndDual X ≅
      Opposite.op ((Ind.yoneda (C := FintypeCat.Skeleton.{0}ᵒᵖ)).obj
        (Opposite.op (X.obj singletonStage))) := by
  letI : IsIso (colimit.ι (X.op ⋙ Ind.yoneda) (Opposite.op singletonStage)) :=
    isIso_ι_of_isTerminal (Under.mkIdInitial.op) (X.op ⋙ Ind.yoneda)
  exact (asIso (colimit.ι (X.op ⋙ Ind.yoneda)
    (Opposite.op singletonStage))).op

private noncomputable def variedSingletonIso :
    finiteDiagramIndDual varied ≅ finiteDiagramIndDual singleton :=
  atInitialIso varied ≪≫ (atInitialIso singleton).symm

private def variedCone :=
  Profinite.limitCone ((varied ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite)

private def singletonCone :=
  Profinite.limitCone ((singleton ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite)

/-- Comparison of two presentations with different finite stages and a common
dual ind-object. -/
noncomputable example : variedCone.pt ≅ singletonCone.pt :=
  indDualRealizationPresentationIso varied (Iso.refl _) variedCone
    (Profinite.limitConeIsLimit _) singleton variedSingletonIso singletonCone
    (Profinite.limitConeIsLimit _)

/-- Naturality transports between the genuinely different supplied diagrams
even when the underlying ind-object map is the identity. -/
example :
    (indDualRealizationComparisonOfIso singleton variedSingletonIso singletonCone
      (Profinite.limitConeIsLimit _)).hom =
      (indDualRealizationComparisonOfIso varied (Iso.refl _) variedCone
        (Profinite.limitConeIsLimit _)).hom ≫
        finiteDiagramIndDualContinuousEquiv varied singleton variedCone
          (Profinite.limitConeIsLimit _) singletonCone (Profinite.limitConeIsLimit _)
          variedSingletonIso.hom := by
  have h := indDualRealizationComparisonOfIso_naturality
    varied (Iso.refl _) singleton variedSingletonIso
    variedCone (Profinite.limitConeIsLimit _)
    singletonCone (Profinite.limitConeIsLimit _)
    (𝟙 (finiteDiagramIndDual varied))
  simpa only [indDualRealization.map_id, Category.id_comp, Iso.refl_inv,
    Category.comp_id] using h

/-- Passing through the second, different presentation and back recovers
the identity comparison on the first limiting cone. -/
example :
    indDualRealizationPresentationIso varied (Iso.refl _) variedCone
        (Profinite.limitConeIsLimit _) singleton variedSingletonIso singletonCone
        (Profinite.limitConeIsLimit _) ≪≫
      indDualRealizationPresentationIso singleton variedSingletonIso singletonCone
        (Profinite.limitConeIsLimit _) varied (Iso.refl _) variedCone
        (Profinite.limitConeIsLimit _) = Iso.refl variedCone.pt := by
  calc
    _ = indDualRealizationPresentationIso varied (Iso.refl _) variedCone
        (Profinite.limitConeIsLimit _) varied (Iso.refl _) variedCone
        (Profinite.limitConeIsLimit _) :=
      indDualRealizationPresentationIso_trans varied (Iso.refl _) variedCone
        (Profinite.limitConeIsLimit _) singleton variedSingletonIso singletonCone
        (Profinite.limitConeIsLimit _) varied (Iso.refl _) variedCone
        (Profinite.limitConeIsLimit _)
    _ = Iso.refl variedCone.pt :=
      indDualRealizationPresentationIso_refl varied (Iso.refl _) variedCone
        (Profinite.limitConeIsLimit _)

/-- A representative of the non-reflexive supplied isomorphism is obtained
from the finite-stage colimit and refined to the concrete initial stage,
then evaluated at each chosen coordinate of the different presentation. -/
example (i : (finiteDiagramIndDual varied).unop.presentation.Iᵒᵖ) :
    ∃ (h : (singleton ⋙ FintypeCat.Skeleton.incl).obj singletonStage ⟶
        (indDualPresentationDiagram (finiteDiagramIndDual varied) ⋙
          FintypeCat.Skeleton.incl).obj i),
      (indDualRealizationComparisonOfIso singleton variedSingletonIso singletonCone
        (Profinite.limitConeIsLimit _)).inv ≫
          (indDualPresentationCone (finiteDiagramIndDual varied)).π.app i =
        singletonCone.π.app singletonStage ≫ FintypeCat.toProfinite.map h := by
  let source := singleton ⋙ FintypeCat.Skeleton.incl
  let target := (indDualPresentationDiagram (finiteDiagramIndDual varied) ⋙
    FintypeCat.Skeleton.incl).obj i
  let classValue := (finiteDiagramIndDualHomMap singleton
    (indDualPresentationDiagram (finiteDiagramIndDual varied))
    (variedSingletonIso.inv ≫
      (indDualPresentationIso (finiteDiagramIndDual varied)).inv)).val i
  obtain ⟨⟨j⟩, h, hh⟩ :=
    Limits.Types.jointly_surjective' (F := stageHom source target) classValue
  change source.obj j ⟶ target at h
  let a : singletonStage ⟶ j := Under.mkIdInitial.to j
  refine ⟨source.map a ≫ h, ?_⟩
  apply indDualRealizationComparisonOfIso_inv_apply_chosen_class
    singleton variedSingletonIso singletonCone (Profinite.limitConeIsLimit _)
      i singletonStage (source.map a ≫ h)
  exact hh.symm.trans (stageHomClass_refine (F := source) target a h)

end ProfiniteGroupsTests.IndDualRealization
