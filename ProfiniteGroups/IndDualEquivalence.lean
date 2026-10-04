/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.IndDualRealization
public import Mathlib.Topology.Category.Profinite.AsLimit

/-!
# Dual ind-objects and profinite spaces

The inverse direction starts with all discrete finite quotients of a profinite
space. Their finite sets are transported through the inverse of the finite-set
skeleton equivalence. The resulting small cofiltered skeletal diagram presents
a dual ind-object, whose realization is isomorphic to the original space.

This fixed-universe equivalence compares profinite spaces, not profinite
groups or an arbitrary pro-category. It uses the generic inverse associated
to a fully faithful and essentially surjective functor; an explicit
isomorphism compares that inverse with the quotient presentation. Finite
stages may be empty, and no projection
of an arbitrary finite diagram is required to be an epimorphism.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, paragraph after
  (1.1.2) (pro-category motivation, not a printed fixed-universe dual-Ind equivalence
  theorem).
- Mathlib, `Mathlib.CategoryTheory.Limits.Indization.Category` and
  `Mathlib.Topology.Category.Profinite.AsLimit` (Ind presentations, finite-set skeleton and
  finite-quotient cone); `IndDualRealization` supplies the preceding comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

/-- The canonical finite quotient diagram, with stages in the finite-set skeleton. -/
noncomputable def skeletalQuotientDiagram (T : Profinite.{u}) :
    DiscreteQuotient T ⥤ FintypeCat.Skeleton.{u} :=
  T.fintypeDiagram ⋙ FintypeCat.Skeleton.equivalence.inverse

/-- Including the skeletal finite quotients recovers the original quotient diagram. -/
noncomputable def skeletalQuotientDiagramIso (T : Profinite.{u}) :
    skeletalQuotientDiagram T ⋙ FintypeCat.Skeleton.incl ≅ T.fintypeDiagram :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft T.fintypeDiagram FintypeCat.Skeleton.equivalence.counitIso ≪≫
      Functor.rightUnitor _

/-- At a finite quotient the diagram comparison is the skeleton counit. -/
@[simp] theorem skeletalQuotientDiagramIso_hom_app
    (T : Profinite.{u}) (S : DiscreteQuotient T) :
    (skeletalQuotientDiagramIso T).hom.app S =
      FintypeCat.Skeleton.equivalence.counitIso.hom.app (T.fintypeDiagram.obj S) := by
  rfl

/-- The reverse comparison returns to the chosen skeletal finite stage. -/
@[simp] theorem skeletalQuotientDiagramIso_inv_app
    (T : Profinite.{u}) (S : DiscreteQuotient T) :
    (skeletalQuotientDiagramIso T).inv.app S =
      FintypeCat.Skeleton.equivalence.counitIso.inv.app (T.fintypeDiagram.obj S) := by
  rfl

/-- The original transition maps intertwine the finite-stage counits. -/
theorem skeletalQuotientDiagram_map_counit
    (T : Profinite.{u}) {S S' : DiscreteQuotient T} (f : S ⟶ S') :
    (skeletalQuotientDiagram T ⋙ FintypeCat.Skeleton.incl).map f ≫
        FintypeCat.Skeleton.equivalence.counitIso.hom.app (T.fintypeDiagram.obj S') =
      FintypeCat.Skeleton.equivalence.counitIso.hom.app (T.fintypeDiagram.obj S) ≫
        T.fintypeDiagram.map f := by
  rw [← skeletalQuotientDiagramIso_hom_app T S,
    ← skeletalQuotientDiagramIso_hom_app T S']
  exact (skeletalQuotientDiagramIso T).hom.naturality f

/-- The cone with point `T` obtained by transporting the ordinary finite-quotient cone
across the skeleton counit. -/
noncomputable def skeletalQuotientCone (T : Profinite.{u}) :
    Cone ((skeletalQuotientDiagram T ⋙ FintypeCat.Skeleton.incl) ⋙
      FintypeCat.toProfinite) :=
  (Cone.postcompose (Functor.isoWhiskerRight (skeletalQuotientDiagramIso T).symm
    FintypeCat.toProfinite).hom).obj T.asLimitCone

/-- The point of the skeletal quotient cone is the original space. -/
@[simp] theorem skeletalQuotientCone_pt (T : Profinite.{u}) :
    (skeletalQuotientCone T).pt = T := rfl

/-- The skeletal coordinate is the original quotient projection followed by the
inverse counit on that finite quotient. -/
theorem skeletalQuotientCone_π (T : Profinite.{u}) (S : DiscreteQuotient T) :
    (skeletalQuotientCone T).π.app S =
      T.asLimitCone.π.app S ≫
        FintypeCat.toProfinite.map
          (FintypeCat.Skeleton.equivalence.counitIso.inv.app
            (T.fintypeDiagram.obj S)) := by
  rfl

/-- Evaluating a skeletal coordinate amounts to quotienting and applying the
inverse skeleton counit at that finite quotient. -/
theorem skeletalQuotientCone_π_apply
    (T : Profinite.{u}) (S : DiscreteQuotient T) (x : T) :
    (skeletalQuotientCone T).π.app S x =
      (FintypeCat.Skeleton.equivalence.counitIso.inv.app
        (T.fintypeDiagram.obj S)) (S.proj x) := by
  rw [skeletalQuotientCone_π]
  rfl

/-- Transport of the canonical finite-quotient limit along the included-diagram
isomorphism. -/
noncomputable def skeletalQuotientConeIsLimit (T : Profinite.{u}) :
    IsLimit (skeletalQuotientCone T) := by
  exact (IsLimit.postcomposeHomEquiv
    (Functor.isoWhiskerRight (skeletalQuotientDiagramIso T).symm FintypeCat.toProfinite)
    T.asLimitCone).symm T.asLimit

/-- Skeletal quotient coordinates detect equality of continuous maps into `T`. -/
theorem skeletalQuotientCone_hom_ext (T : Profinite.{u}) {U : Profinite.{u}}
    {f g : U ⟶ T}
    (h : ∀ S : DiscreteQuotient T,
      f ≫ (skeletalQuotientCone T).π.app S =
        g ≫ (skeletalQuotientCone T).π.app S) : f = g :=
  (skeletalQuotientConeIsLimit T).hom_ext h

/-- The dual ind-object specified by the skeletal finite quotients of `T`. -/
noncomputable def skeletalQuotientIndDual (T : Profinite.{u}) :
    (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ :=
  finiteDiagramIndDual (skeletalQuotientDiagram T)

/-- The realized skeletal quotient presentation is the original profinite space. -/
noncomputable def skeletalQuotientRealizationIso (T : Profinite.{u}) :
    indDualRealization.obj (skeletalQuotientIndDual T) ≅ T :=
  indDualRealizationComparison (skeletalQuotientDiagram T)
    (skeletalQuotientCone T) (skeletalQuotientConeIsLimit T)

/-- A representative of the comparison at a finite quotient computes its
projection from the chosen presentation of the dual ind-object. -/
theorem skeletalQuotientRealizationIso_hom_comp_π
    (T : Profinite.{u}) (S : DiscreteQuotient T)
    (i : (skeletalQuotientIndDual T).unop.presentation.Iᵒᵖ)
    (h : (indDualPresentationDiagram (skeletalQuotientIndDual T) ⋙
      FintypeCat.Skeleton.incl).obj i ⟶
      (skeletalQuotientDiagram T ⋙ FintypeCat.Skeleton.incl).obj S)
    (hi : (finiteDiagramIndDualHomMap
      (indDualPresentationDiagram (skeletalQuotientIndDual T))
      (skeletalQuotientDiagram T)
      (indDualPresentationIso (skeletalQuotientIndDual T)).hom).val S =
        stageHomClass (indDualPresentationDiagram (skeletalQuotientIndDual T) ⋙
          FintypeCat.Skeleton.incl) _ i h) :
    (skeletalQuotientRealizationIso T).hom ≫ (skeletalQuotientCone T).π.app S =
      (indDualPresentationCone (skeletalQuotientIndDual T)).π.app i ≫
        FintypeCat.toProfinite.map h :=
  indDualRealizationComparison_apply_class _ _ _ S i h hi

/-- A representative of the reverse comparison evaluates at a chosen
presentation coordinate, without canceling a quotient projection. -/
theorem skeletalQuotientRealizationIso_inv_comp_π
    (T : Profinite.{u})
    (i : (skeletalQuotientIndDual T).unop.presentation.Iᵒᵖ)
    (S : DiscreteQuotient T)
    (h : (skeletalQuotientDiagram T ⋙ FintypeCat.Skeleton.incl).obj S ⟶
      (indDualPresentationDiagram (skeletalQuotientIndDual T) ⋙
        FintypeCat.Skeleton.incl).obj i)
    (hi : (finiteDiagramIndDualHomMap (skeletalQuotientDiagram T)
      (indDualPresentationDiagram (skeletalQuotientIndDual T))
      (indDualPresentationIso (skeletalQuotientIndDual T)).inv).val i =
        stageHomClass (skeletalQuotientDiagram T ⋙ FintypeCat.Skeleton.incl) _ S h) :
    (skeletalQuotientRealizationIso T).inv ≫
        (indDualPresentationCone (skeletalQuotientIndDual T)).π.app i =
      (skeletalQuotientCone T).π.app S ≫ FintypeCat.toProfinite.map h :=
  indDualRealizationComparison_inv_apply_class _ _ _ i S h hi

/-- Every profinite space is in the essential image of dual-Ind realization. -/
theorem indDualRealizationEssSurj : indDualRealization.{u}.EssSurj :=
  ⟨fun T => ⟨skeletalQuotientIndDual T, ⟨skeletalQuotientRealizationIso T⟩⟩⟩

/-- Fully faithful realization together with the skeletal quotient presentation
gives an equivalence of categories.

Combines Mathlib’s finite-quotient presentation with fully faithful realization; the remark
in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1 is motivation, not
this equivalence theorem. -/
noncomputable instance indDualRealizationIsEquivalence :
    indDualRealization.{u}.IsEquivalence where
  faithful := indDualRealizationFullyFaithful.faithful
  full := indDualRealizationFullyFaithful.full
  essSurj := indDualRealizationEssSurj

/-- The fixed-universe equivalence with the already defined realization as
its forward functor.

This fixed-universe equivalence concerns profinite *spaces*, not groups, arbitrary
pro-categories or multiple universes. Mathlib’s Ind and finite-quotient presentations
supply the approach; the pro-category remark in Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Ch. I §1 is motivation only. -/
noncomputable def indDualEquivalence :
    (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ ≌ Profinite.{u} :=
  indDualRealization.asEquivalence

/-- The forward functor of the equivalence is the existing realization. -/
@[simp] theorem indDualEquivalence_functor :
    indDualEquivalence.{u}.functor = indDualRealization := rfl

/-- Compare the generic inverse's chosen object with the specified skeletal
quotient presentation; no equality between their choices is assumed. -/
noncomputable def indDualEquivalenceInverseIso (T : Profinite.{u}) :
    indDualEquivalence.inverse.obj T ≅ skeletalQuotientIndDual T :=
  indDualRealization.preimageIso
    (indDualEquivalence.counitIso.app T ≪≫ (skeletalQuotientRealizationIso T).symm)

/-- The inverse comparison, after realization, is the counit followed by
the reverse skeletal-quotient comparison. -/
theorem indDualEquivalenceInverseIso_map_hom (T : Profinite.{u}) :
    indDualRealization.map (indDualEquivalenceInverseIso T).hom =
      (indDualEquivalence.counitIso.app T).hom ≫
        (skeletalQuotientRealizationIso T).inv := by
  simp only [indDualEquivalenceInverseIso, Functor.preimageIso_hom,
    Functor.map_preimage]
  rfl

/-- The generic inverse sends a continuous map to its fully faithful
preimage, conjugated by the chosen counits. -/
theorem indDualEquivalence_inverse_map {T U : Profinite.{u}} (f : T ⟶ U) :
    indDualRealization.map (indDualEquivalence.inverse.map f) =
      indDualEquivalence.counitIso.hom.app T ≫ f ≫
        indDualEquivalence.counitIso.inv.app U := by
  simpa only [indDualEquivalence_functor, Functor.comp_obj, Functor.comp_map,
    Functor.id_map] using
    (NatIso.naturality_2 (α := indDualEquivalence.counitIso) (f := f)).symm

/-- The inverse sends a realized map to the original map, conjugated by
the unit isomorphisms of its source and target. -/
theorem indDualEquivalence_unit_map
    {Q R : (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ} (f : Q ⟶ R) :
    indDualEquivalence.inverse.map (indDualRealization.map f) =
      indDualEquivalence.unitIso.inv.app Q ≫ f ≫
        indDualEquivalence.unitIso.hom.app R := by
  simpa only [indDualEquivalence_functor, Functor.comp_obj, Functor.comp_map,
    Functor.id_map] using
    (NatIso.naturality_1 (α := indDualEquivalence.unitIso) (f := f)).symm

end Profinite
