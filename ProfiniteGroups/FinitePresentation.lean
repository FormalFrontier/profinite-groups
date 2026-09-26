/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Topology.Category.LightProfinite.Injective
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Presentations of profinite maps by finite maps

This file presents an injective or surjective map of profinite spaces as the
limit of a natural transformation between cofiltered diagrams of finite
discrete spaces whose component maps are respectively injective or
surjective.

The maps here are morphisms of `Profinite` (profinite *spaces*), not
homomorphisms or finite presentations of profinite groups.
-/

@[expose] public section

open CategoryTheory Function

namespace Profinite.FinitePresentation

universe u

variable {X Y : Profinite.{u}} (f : X ⟶ Y)

/-! ## Injective maps -/

/-- The source stage over a finite quotient of the target. -/
def injectiveSourceStage (B : DiscreteQuotient Y) : DiscreteQuotient X :=
  B.comap f.hom.hom

/-- The map from a pulled-back source stage to its target stage. -/
def injectiveStageMap (B : DiscreteQuotient Y) : injectiveSourceStage f B → B :=
  DiscreteQuotient.map f.hom.hom le_rfl

/-- Pull finite target quotients back to finite source quotients. -/
def injectiveIndex : DiscreteQuotient Y ⥤ DiscreteQuotient X where
  obj B := injectiveSourceStage f B
  map g := homOfLE (DiscreteQuotient.comap_mono f.hom.hom g.le)

/-- A pulled-back finite stage maps injectively to its target stage. -/
theorem injectiveStageMap_injective (B : DiscreteQuotient Y) :
    Injective (injectiveStageMap f B) := by
  rintro ⟨x⟩ ⟨y⟩ h
  change B.proj (f x) = B.proj (f y) at h
  apply Quotient.sound
  change B.toSetoid (f x) (f y)
  exact Quotient.exact h

/-- If `f` is injective, pulled-back target quotients are cofinal among the
finite quotients of the source. -/
theorem injectiveIndex_initial (hf : Injective f) :
    (injectiveIndex f).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered (injectiveIndex f)
  · intro A
    cases isEmpty_or_nonempty X with
    | inl hX =>
        refine ⟨⊤, ⟨homOfLE ?_⟩⟩
        intro x
        exact (hX.false x).elim
    | inr hX =>
        let _ := hX
        obtain ⟨k, hk_cont, _, hk⟩ :=
          Profinite.exists_lift_of_finite_of_injective_of_surjective
            f f.hom.hom.continuous hf
            (fun _ : A ↦ Unit.unit) (surjective_to_subsingleton _)
            A.proj A.proj_continuous (fun _ : Y ↦ Unit.unit) continuous_const
            (by rfl)
        let k' : LocallyConstant Y A :=
          ⟨k, (IsLocallyConstant.iff_continuous _).mpr hk_cont⟩
        refine ⟨k'.discreteQuotient, ⟨homOfLE ?_⟩⟩
        intro x y hxy
        apply Quotient.exact
        change (injectiveSourceStage f k'.discreteQuotient).toSetoid x y at hxy
        change (k'.discreteQuotient.comap f.hom.hom).toSetoid x y at hxy
        change k'.discreteQuotient.toSetoid (f x) (f y) at hxy
        change k (f x) = k (f y) at hxy
        have hxy' : k (f x) = k (f y) := hxy
        have hx : k (f x) = A.proj x := by
          simpa only [Function.comp_apply] using congr_fun hk x
        have hy : k (f y) = A.proj y := by
          simpa only [Function.comp_apply] using congr_fun hk y
        exact hx.symm.trans (hxy'.trans hy)
  · intro A B s s'
    exact ⟨B, 𝟙 B, Subsingleton.elim _ _⟩

/-- The natural transformation of finite stages induced by an injective
profinite map. The definition makes sense without the injectivity hypothesis. -/
def injectiveFintypeMap :
    injectiveIndex f ⋙ X.fintypeDiagram ⟶ Y.fintypeDiagram where
  app B := FintypeCat.homMk (injectiveStageMap f B)
  naturality _ _ _ := by
    ext x
    rcases x with ⟨x⟩
    rfl

/-- The source profinite diagram indexed by finite target quotients. -/
abbrev injectiveSourceDiagram : DiscreteQuotient Y ⥤ Profinite.{u} :=
  injectiveIndex f ⋙ X.diagram

/-- The natural transformation of finite discrete profinite stages induced by
`f`. -/
def injectiveDiagramMap : injectiveSourceDiagram f ⟶ Y.diagram :=
  Functor.whiskerRight (injectiveFintypeMap f) FintypeCat.toProfinite

/-- The source limit cone reindexed by finite target quotients. -/
def injectiveSourceCone : Limits.Cone (injectiveSourceDiagram f) :=
  X.asLimitCone.whisker (injectiveIndex f)

/-- The reindexed source cone is a limit cone when `f` is injective. -/
noncomputable def injectiveSourceLimit (hf : Injective f) :
    Limits.IsLimit (injectiveSourceCone f) := by
  letI := injectiveIndex_initial f hf
  exact (Functor.Initial.isLimitWhiskerEquiv (injectiveIndex f) X.asLimitCone).symm X.asLimit

/-- Every component of the finite-stage transformation for an injective map is
injective. -/
theorem injectiveFintypeMap_app_injective (B : DiscreteQuotient Y) :
    Injective ((injectiveFintypeMap f).app B) :=
  injectiveStageMap_injective f B

/-- The map of limit cones induced by the finite-stage transformation is the
original profinite map. -/
def injectiveConeHom :
    (Limits.Cone.postcompose (injectiveDiagramMap f)).obj (injectiveSourceCone f) ⟶
      Y.asLimitCone where
  hom := f
  w B := by
    ext x
    rfl

/-! ## Surjective maps -/

/-- A common finite-stage index for a profinite map consists of a source
quotient refining the pullback of a target quotient. The target projection
composed with the map factors through the source projection. -/
abbrev SurjectiveIndex :=
  { P : DiscreteQuotient X × DiscreteQuotient Y // P.1 ≤ P.2.comap f.hom.hom }

/-- The terminal source and target quotients provide a common stage for any map. -/
instance surjectiveIndex_nonempty : Nonempty (SurjectiveIndex f) := by
  refine ⟨⟨(⊤, ⊤), ?_⟩⟩
  intro _ _ _
  trivial

/-- Two finite source/target quotient pairs admit a common refinement,
providing the cofiltered index needed for the surjective presentation. -/
instance surjectiveIndex_isCodirected : IsCodirectedOrder (SurjectiveIndex f) where
  directed P Q := by
    refine ⟨⟨(P.1.1 ⊓ Q.1.1, P.1.2 ⊓ Q.1.2), ?_⟩, ?_, ?_⟩
    · intro _ _ h
      exact ⟨P.2 h.1, Q.2 h.2⟩
    · exact ⟨inf_le_left, inf_le_left⟩
    · exact ⟨inf_le_right, inf_le_right⟩

/-- Project a common finite-stage index to its source quotient. -/
def surjectiveSourceIndex : SurjectiveIndex f ⥤ DiscreteQuotient X :=
  (show Monotone (fun P : SurjectiveIndex f ↦ P.1.1) from fun _ _ h ↦ h.1).functor

/-- Project a common finite-stage index to its target quotient. -/
def surjectiveTargetIndex : SurjectiveIndex f ⥤ DiscreteQuotient Y :=
  (show Monotone (fun P : SurjectiveIndex f ↦ P.1.2) from fun _ _ h ↦ h.2).functor

/-- The source projection from common finite stages is initial. -/
theorem surjectiveSourceIndex_initial : (surjectiveSourceIndex f).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered (surjectiveSourceIndex f)
  · intro A
    refine ⟨⟨(A, ⊤), ?_⟩, ⟨homOfLE le_rfl⟩⟩
    intro _ _ _
    trivial
  · intro A P s s'
    exact ⟨P, 𝟙 P, Subsingleton.elim _ _⟩

/-- The target projection from common finite stages is initial. -/
theorem surjectiveTargetIndex_initial : (surjectiveTargetIndex f).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered (surjectiveTargetIndex f)
  · intro B
    exact ⟨⟨(B.comap f.hom.hom, B), le_rfl⟩, ⟨homOfLE le_rfl⟩⟩
  · intro B P s s'
    exact ⟨P, 𝟙 P, Subsingleton.elim _ _⟩

/-- The natural transformation between the common finite source and target
stages. -/
def surjectiveFintypeMap :
    surjectiveSourceIndex f ⋙ X.fintypeDiagram ⟶
      surjectiveTargetIndex f ⋙ Y.fintypeDiagram where
  app P := FintypeCat.homMk (DiscreteQuotient.map f.hom.hom P.2)
  naturality _ _ _ := by
    ext x
    rcases x with ⟨x⟩
    rfl

/-- Every component of the common finite-stage transformation is surjective
when the original profinite map is surjective. -/
theorem surjectiveFintypeMap_app_surjective (hf : Surjective f) (P : SurjectiveIndex f) :
    Surjective ((surjectiveFintypeMap f).app P) := by
  rintro b
  obtain ⟨y, rfl⟩ := P.1.2.proj_surjective b
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨P.1.1.proj x, rfl⟩

/-- The source profinite diagram over the common finite-stage index. -/
abbrev surjectiveSourceDiagram : SurjectiveIndex f ⥤ Profinite.{u} :=
  surjectiveSourceIndex f ⋙ X.diagram

/-- The target profinite diagram over the common finite-stage index. -/
abbrev surjectiveTargetDiagram : SurjectiveIndex f ⥤ Profinite.{u} :=
  surjectiveTargetIndex f ⋙ Y.diagram

/-- The natural transformation of finite discrete profinite stages induced by
`f`. -/
def surjectiveDiagramMap : surjectiveSourceDiagram f ⟶ surjectiveTargetDiagram f :=
  Functor.whiskerRight (surjectiveFintypeMap f) FintypeCat.toProfinite

/-- The source limit cone over the common finite-stage index. -/
def surjectiveSourceCone : Limits.Cone (surjectiveSourceDiagram f) :=
  X.asLimitCone.whisker (surjectiveSourceIndex f)

/-- The target limit cone over the common finite-stage index. -/
def surjectiveTargetCone : Limits.Cone (surjectiveTargetDiagram f) :=
  Y.asLimitCone.whisker (surjectiveTargetIndex f)

/-- The common-index source cone is a limit cone. -/
noncomputable def surjectiveSourceLimit :
    Limits.IsLimit (surjectiveSourceCone f) := by
  letI := surjectiveSourceIndex_initial f
  exact
    (Functor.Initial.isLimitWhiskerEquiv (surjectiveSourceIndex f) X.asLimitCone).symm X.asLimit

/-- The common-index target cone is a limit cone. -/
noncomputable def surjectiveTargetLimit :
    Limits.IsLimit (surjectiveTargetCone f) := by
  letI := surjectiveTargetIndex_initial f
  exact
    (Functor.Initial.isLimitWhiskerEquiv (surjectiveTargetIndex f) Y.asLimitCone).symm Y.asLimit

/-- The map of common-index limit cones induced by the finite-stage
transformation is the original profinite map. -/
def surjectiveConeHom :
    (Limits.Cone.postcompose (surjectiveDiagramMap f)).obj (surjectiveSourceCone f) ⟶
      surjectiveTargetCone f where
  hom := f
  w P := by
    ext x
    rfl

end Profinite.FinitePresentation
