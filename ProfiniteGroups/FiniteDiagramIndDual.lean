/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FiniteDiagramHomLimit
public import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Finite-space diagrams and dual ind-objects

A cofiltered diagram in the finite-set skeleton gives an object of the opposite
of the ind-category of the opposite skeleton. For two specified diagrams, the
coordinate of a morphism is a class of maps from a source stage to a target stage.
The comparison with compatible classes specifies coordinate-level
composition and naturality laws. Only diagrams with small,
nonempty cofiltered indices are presented this way; the existing continuous-map
comparison allows a more general target index. No presentation-independent
pro-category or cross-universe equivalence is asserted.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1 (pro-category
  motivation, not this explicit dual-Ind comparison).
- Mathlib, `Mathlib.CategoryTheory.Limits.Indization.Category` (Ind presentations, Yoneda
  and pointwise colimits); `FiniteDiagramHomLimit` supplies the finite-stage map
  comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Opposite

universe u

namespace Profinite

variable {I J K : Type u} [SmallCategory I] [IsCofiltered I]
    [SmallCategory J] [IsCofiltered J] [SmallCategory K] [IsCofiltered K]

/-- The dual ind-object presented by a cofiltered diagram of finite sets. -/
noncomputable def finiteDiagramIndDual (X : I ⥤ FintypeCat.Skeleton.{u}) :
    (Ind FintypeCat.Skeleton.{u}ᵒᵖ)ᵒᵖ :=
  Opposite.op ((Ind.lim Iᵒᵖ).obj X.op)

/-- Fixed-index diagram maps induce maps of their dual ind-objects. -/
noncomputable def finiteDiagramIndDualMap {X X' : I ⥤ FintypeCat.Skeleton.{u}}
    (a : X ⟶ X') : finiteDiagramIndDual X ⟶ finiteDiagramIndDual X' :=
  ((Ind.lim Iᵒᵖ).map (NatTrans.op a)).op

/-- The identity diagram map induces the identity on its dual ind-object. -/
@[simp] theorem finiteDiagramIndDualMap_id (X : I ⥤ FintypeCat.Skeleton.{u}) :
    finiteDiagramIndDualMap (𝟙 X) = 𝟙 (finiteDiagramIndDual X) := by
  change ((Ind.lim Iᵒᵖ).map (𝟙 X.op)).op =
    (𝟙 ((Ind.lim Iᵒᵖ).obj X.op)).op
  rw [(Ind.lim Iᵒᵖ).map_id X.op]

/-- Composition of fixed-index diagram maps induces composition in the same order
on their dual ind-objects. -/
@[simp] theorem finiteDiagramIndDualMap_comp {X X' X'' : I ⥤ FintypeCat.Skeleton.{u}}
    (a : X ⟶ X') (b : X' ⟶ X'') :
    finiteDiagramIndDualMap (a ≫ b) =
      finiteDiagramIndDualMap a ≫ finiteDiagramIndDualMap b := by
  simp only [finiteDiagramIndDualMap, NatTrans.op_comp, Functor.map_comp, op_comp]
  rfl

/-- The presheaf map obtained by unopping a dual ind-object morphism,
including both ind-colimit presentation isomorphisms. -/
noncomputable def finiteDiagramIndDualPresheafMap
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y) :
    colimit (Y.op ⋙ yoneda) ⟶ colimit (X.op ⋙ yoneda) :=
  ((Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ) (I := Jᵒᵖ)).app Y.op).inv ≫
    (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map f.unop ≫
      ((Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ) (I := Iᵒᵖ)).app X.op).hom

/-- Include a skeletal Yoneda stage map in the finite-set stage-hom diagram. -/
noncomputable def finiteDiagramIndDualStageMap
    (X : I ⥤ FintypeCat.Skeleton.{u}) (s : FintypeCat.Skeleton.{u}) :
    ((X.op ⋙ yoneda) ⋙
      (evaluation _ _).obj (Opposite.op (Opposite.op s))) ⟶
      stageHom (X ⋙ FintypeCat.Skeleton.incl)
        (FintypeCat.Skeleton.incl.obj s) where
  app i := by
    dsimp [stageHom, evaluation, yoneda]
    exact ↾(fun (h : Opposite.op s ⟶ Opposite.op (X.obj i.unop)) =>
      FintypeCat.Skeleton.incl.map h.unop)
  naturality := by
    intro i j a
    ext h
    rfl

/-- Interpret the value of the pointwise Yoneda colimit as a class of
finite-set maps out of the specified diagram. -/
noncomputable def finiteDiagramIndDualStageValue
    (X : I ⥤ FintypeCat.Skeleton.{u}) (s : FintypeCat.Skeleton.{u})
    (value : (colimit (X.op ⋙ yoneda)).obj (Opposite.op (Opposite.op s))) :
    colimit (stageHom (X ⋙ FintypeCat.Skeleton.incl)
      (FintypeCat.Skeleton.incl.obj s)) :=
  (colim.map (finiteDiagramIndDualStageMap X s))
    ((colimitObjIsoColimitCompEvaluation (X.op ⋙ yoneda)
      (Opposite.op (Opposite.op s))).hom value)

omit [IsCofiltered I] in
/-- A pointwise Yoneda-colimit injection maps to the class of the
corresponding skeletal stage map. -/
theorem finiteDiagramIndDualStageValue_ι
    (X : I ⥤ FintypeCat.Skeleton.{u}) (s : FintypeCat.Skeleton.{u})
    (i : I) (h : X.obj i ⟶ s) :
    finiteDiagramIndDualStageValue X s
      ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ h.op) =
        stageHomClass (X ⋙ FintypeCat.Skeleton.incl)
          (FintypeCat.Skeleton.incl.obj s) i
          (FintypeCat.Skeleton.incl.map h) := by
  unfold finiteDiagramIndDualStageValue
  simp only [colim_map, colim_obj]
  calc
    _ = colimMap (finiteDiagramIndDualStageMap X s)
        (colimit.ι ((X.op ⋙ yoneda) ⋙
          (evaluation _ _).obj (Opposite.op (Opposite.op s))) (Opposite.op i) h.op) := by
            congr 1
            exact ((comp_apply ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _)
              (colimitObjIsoColimitCompEvaluation (X.op ⋙ yoneda)
                (Opposite.op (Opposite.op s))).hom h.op).symm).trans
              (ConcreteCategory.congr_hom (colimitObjIsoColimitCompEvaluation_ι_app_hom
                (X.op ⋙ yoneda) (Opposite.op i) (Opposite.op (Opposite.op s))) h.op)
    _ = _ := by
      rw [colimit.ι_map_apply]
      rfl

omit [IsCofiltered I] in
private theorem finiteDiagramIndDualStageMap_isIso
    (X : I ⥤ FintypeCat.Skeleton.{u}) (s : FintypeCat.Skeleton.{u}) :
    IsIso (finiteDiagramIndDualStageMap X s) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro i
  apply (isIso_iff_bijective _).2
  change Function.Bijective (fun h : Opposite.op s ⟶ Opposite.op (X.obj i.unop) =>
    FintypeCat.Skeleton.incl.map h.unop)
  constructor
  · intro h k heq
    simpa using congrArg (fun g : X.obj i.unop ⟶ s => g.op)
      ((FintypeCat.Skeleton.incl).map_injective heq)
  · intro g
    obtain ⟨h, rfl⟩ := (FintypeCat.Skeleton.incl).map_surjective g
    exact ⟨h.op, rfl⟩

private noncomputable def finiteDiagramIndDualStageValueEquiv
    (X : I ⥤ FintypeCat.Skeleton.{u}) (s : FintypeCat.Skeleton.{u}) :
    (colimit (X.op ⋙ yoneda)).obj (Opposite.op (Opposite.op s)) ≃
      colimit (stageHom (X ⋙ FintypeCat.Skeleton.incl)
        (FintypeCat.Skeleton.incl.obj s)) := by
  letI := finiteDiagramIndDualStageMap_isIso X s
  exact (colimitObjIsoColimitCompEvaluation (X.op ⋙ yoneda)
    (Opposite.op (Opposite.op s))).toEquiv.trans
      (colim.mapIso (asIso (finiteDiagramIndDualStageMap X s))).toEquiv

omit [IsCofiltered I] in
private theorem finiteDiagramIndDualStageValueEquiv_apply
    (X : I ⥤ FintypeCat.Skeleton.{u}) (s : FintypeCat.Skeleton.{u})
    (value : (colimit (X.op ⋙ yoneda)).obj (Opposite.op (Opposite.op s))) :
    finiteDiagramIndDualStageValueEquiv X s value =
      finiteDiagramIndDualStageValue X s value := rfl

omit [IsCofiltered I] in
private theorem finiteDiagramIndDualStageValue_ι_surjective
    (X : I ⥤ FintypeCat.Skeleton.{u}) (s : FintypeCat.Skeleton.{u})
    (value : (colimit (X.op ⋙ yoneda)).obj (Opposite.op (Opposite.op s))) :
    ∃ (i : I) (h : X.obj i ⟶ s),
      ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ h.op) = value := by
  let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ yoneda)
    (Opposite.op (Opposite.op s))
  obtain ⟨i, h, hi⟩ := Types.jointly_surjective' (e.hom value)
  refine ⟨i.unop, h.unop, ?_⟩
  apply e.toEquiv.injective
  change e.hom ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i.unop)).app _ h.unop.op) =
    e.hom value
  rw [Quiver.Hom.op_unop]
  calc
    _ = (((colimit.ι (X.op ⋙ yoneda) i).app _) ≫ e.hom) h :=
      (comp_apply ((colimit.ι (X.op ⋙ yoneda) i).app _) e.hom h).symm
    _ = (colimit.ι ((X.op ⋙ yoneda) ⋙
        (evaluation _ _).obj (Opposite.op (Opposite.op s))) i) h :=
      ConcreteCategory.congr_hom (colimitObjIsoColimitCompEvaluation_ι_app_hom
        (X.op ⋙ yoneda) i (Opposite.op (Opposite.op s))) h
    _ = _ := hi

omit [IsCofiltered I] in
private theorem finiteDiagramIndDualStageValue_naturality
    (X : I ⥤ FintypeCat.Skeleton.{u}) {s t : FintypeCat.Skeleton.{u}}
    (a : s ⟶ t)
    (value : (colimit (X.op ⋙ yoneda)).obj (Opposite.op (Opposite.op s))) :
    stageHomPost (F := X ⋙ FintypeCat.Skeleton.incl)
        (FintypeCat.Skeleton.incl.map a) (finiteDiagramIndDualStageValue X s value) =
      finiteDiagramIndDualStageValue X t
        ((colimit (X.op ⋙ yoneda)).map a.op.op value) := by
  obtain ⟨i, h, rfl⟩ := finiteDiagramIndDualStageValue_ι_surjective X s value
  rw [finiteDiagramIndDualStageValue_ι, stageHomPost_class]
  have hn := congrArg (fun f => f h.op)
    ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).naturality a.op.op)
  change ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ (h ≫ a).op) =
    (colimit (X.op ⋙ yoneda)).map a.op.op
      ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ h.op) at hn
  rw [← hn, finiteDiagramIndDualStageValue_ι]
  rfl

private theorem finiteDiagramIndDualPresheafMap_bijective
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u}) :
    Function.Bijective (finiteDiagramIndDualPresheafMap X Y) := by
  let eX := (Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
    (I := Iᵒᵖ)).app X.op
  let eY := (Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
    (I := Jᵒᵖ)).app Y.op
  constructor
  · intro f g h
    apply Quiver.Hom.unop_inj
    apply (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map_injective
    have hh := congrArg (fun η => eY.hom ≫ η ≫ eX.inv) h
    change eY.hom ≫
        (eY.inv ≫ (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map f.unop ≫ eX.hom) ≫
          eX.inv =
      eY.hom ≫
        (eY.inv ≫ (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map g.unop ≫ eX.hom) ≫
          eX.inv at hh
    simp only [← Category.assoc, eY.hom_inv_id, Category.id_comp] at hh
    exact (cancel_mono eX.hom).1 ((cancel_mono eX.inv).1 hh)
  · intro η
    obtain ⟨p, hp⟩ := (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map_surjective
      (eY.hom ≫ η ≫ eX.inv)
    refine ⟨p.op, ?_⟩
    change eY.inv ≫ (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map p.op.unop ≫
      eX.hom = η
    rw [Quiver.Hom.unop_op, hp]
    simp [Category.assoc]

private theorem finiteDiagramIndDualPresheafMap_id
    (X : I ⥤ FintypeCat.Skeleton.{u}) :
    finiteDiagramIndDualPresheafMap X X (𝟙 (finiteDiagramIndDual X)) =
      𝟙 (colimit (X.op ⋙ yoneda)) := by
  change ((Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
      (I := Iᵒᵖ)).app X.op).inv ≫
    (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map
      (𝟙 ((Ind.lim Iᵒᵖ).obj X.op)) ≫
    ((Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
      (I := Iᵒᵖ)).app X.op).hom = 𝟙 _
  simp

private theorem finiteDiagramIndDualPresheafMap_comp
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (Z : K ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    (g : finiteDiagramIndDual Y ⟶ finiteDiagramIndDual Z) :
    finiteDiagramIndDualPresheafMap X Z (f ≫ g) =
      finiteDiagramIndDualPresheafMap Y Z g ≫
        finiteDiagramIndDualPresheafMap X Y f := by
  let f' : (Ind.lim Jᵒᵖ).obj Y.op ⟶ (Ind.lim Iᵒᵖ).obj X.op := f.unop
  let g' : (Ind.lim Kᵒᵖ).obj Z.op ⟶ (Ind.lim Jᵒᵖ).obj Y.op := g.unop
  let eX := (Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
    (I := Iᵒᵖ)).app X.op
  let eY := (Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
    (I := Jᵒᵖ)).app Y.op
  let eZ := (Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
    (I := Kᵒᵖ)).app Z.op
  change eZ.inv ≫ (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map (g' ≫ f') ≫
      eX.hom =
    (eZ.inv ≫ (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map g' ≫ eY.hom) ≫
      (eY.inv ≫ (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map f' ≫ eX.hom)
  rw [Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem finiteDiagramIndDualPresheafMap_map
    {X X' : I ⥤ FintypeCat.Skeleton.{u}} (a : X ⟶ X') :
    finiteDiagramIndDualPresheafMap X X' (finiteDiagramIndDualMap a) =
      colim.map (Functor.whiskerRight (NatTrans.op a) yoneda) := by
  let eX := (Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
    (I := Iᵒᵖ)).app X.op
  let eX' := (Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
    (I := Iᵒᵖ)).app X'.op
  have hnat := (Ind.limCompInclusion (C := FintypeCat.Skeleton.{u}ᵒᵖ)
    (I := Iᵒᵖ)).hom.naturality (NatTrans.op a)
  change (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map
      ((Ind.lim Iᵒᵖ).map (NatTrans.op a)) ≫ eX.hom =
    eX'.hom ≫ colim.map (Functor.whiskerRight (NatTrans.op a) yoneda) at hnat
  change eX'.inv ≫ (Ind.inclusion FintypeCat.Skeleton.{u}ᵒᵖ).map
      ((Ind.lim Iᵒᵖ).map (NatTrans.op a)) ≫ eX.hom =
    colim.map (Functor.whiskerRight (NatTrans.op a) yoneda)
  rw [hnat]
  simp

/-- The class at a target stage is obtained by applying the included presheaf
transformation to the Yoneda identity, then taking the pointwise colimit and
including skeletal stage maps into finite sets. -/
noncomputable def finiteDiagramIndDualHomMap
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y) :
    ((Y ⋙ FintypeCat.Skeleton.incl) ⋙
      stageHomFunctor (X ⋙ FintypeCat.Skeleton.incl)).sections :=
  ⟨fun j => finiteDiagramIndDualStageValue X (Y.obj j)
    (limit.π (Y.op.op ⋙ colimit (X.op ⋙ yoneda))
      (Opposite.op (Opposite.op j))
      (colimitYonedaHomEquiv Y.op (colimit (X.op ⋙ yoneda))
        (finiteDiagramIndDualPresheafMap X Y f))), by
    intro j k a
    change stageHomPost (F := X ⋙ FintypeCat.Skeleton.incl)
        (FintypeCat.Skeleton.incl.map (Y.map a))
        (finiteDiagramIndDualStageValue X (Y.obj j)
          (limit.π (Y.op.op ⋙ colimit (X.op ⋙ yoneda)) (Opposite.op (Opposite.op j))
            (colimitYonedaHomEquiv Y.op (colimit (X.op ⋙ yoneda))
              (finiteDiagramIndDualPresheafMap X Y f)))) =
      finiteDiagramIndDualStageValue X (Y.obj k)
        (limit.π (Y.op.op ⋙ colimit (X.op ⋙ yoneda)) (Opposite.op (Opposite.op k))
          (colimitYonedaHomEquiv Y.op (colimit (X.op ⋙ yoneda))
            (finiteDiagramIndDualPresheafMap X Y f)))
    rw [finiteDiagramIndDualStageValue_naturality]
    congr 1
    let value := colimitYonedaHomEquiv Y.op (colimit (X.op ⋙ yoneda))
      (finiteDiagramIndDualPresheafMap X Y f)
    change ((Y.op.op ⋙ colimit (X.op ⋙ yoneda)).map a.op.op)
      (limit.π (Y.op.op ⋙ colimit (X.op ⋙ yoneda))
        (Opposite.op (Opposite.op j)) value) =
      (limit.π (Y.op.op ⋙ colimit (X.op ⋙ yoneda))
        (Opposite.op (Opposite.op k))) value
    exact ((comp_apply (limit.π (Y.op.op ⋙ colimit (X.op ⋙ yoneda))
      (Opposite.op (Opposite.op j)))
      ((Y.op.op ⋙ colimit (X.op ⋙ yoneda)).map a.op.op) value).symm).trans
      (ConcreteCategory.congr_hom
        (limit.w (Y.op.op ⋙ colimit (X.op ⋙ yoneda)) a.op.op) value)⟩

/-- The finite-stage class at a target object, with the precise Yoneda identity
and pointwise-colimit coordinate used by the comparison. -/
theorem finiteDiagramIndDualHomMap_apply
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y) (j : J) :
    (finiteDiagramIndDualHomMap X Y f).val j =
      finiteDiagramIndDualStageValue X (Y.obj j)
        ((finiteDiagramIndDualPresheafMap X Y f).app
          (Opposite.op (Y.op.obj (Opposite.op j)))
          ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ (𝟙 _))) := by
  dsimp only [finiteDiagramIndDualHomMap]
  exact congrArg
    (finiteDiagramIndDualStageValue X (Y.obj j))
    (colimitYonedaHomEquiv_π_apply Y.op (colimit (X.op ⋙ yoneda))
      (finiteDiagramIndDualPresheafMap X Y f) (Opposite.op (Opposite.op j)))

/-- A representative of the Yoneda-identity coordinate gives the
corresponding finite-stage class at that target object. -/
theorem finiteDiagramIndDualHomMap_apply_class
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    (j : J) (i : I) (h : X.obj i ⟶ Y.obj j)
    (hf : (finiteDiagramIndDualPresheafMap X Y f).app
        (Opposite.op (Y.op.obj (Opposite.op j)))
        ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ (𝟙 _)) =
      (colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ h.op) :
    (finiteDiagramIndDualHomMap X Y f).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl)
        ((Y ⋙ FintypeCat.Skeleton.incl).obj j) i
          (FintypeCat.Skeleton.incl.map h) := by
  rw [finiteDiagramIndDualHomMap_apply, hf, finiteDiagramIndDualStageValue_ι]
  simp only [Functor.comp_obj]
  rfl

private theorem finiteDiagramIndDualHomMap_apply_ι_of_class
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    (j : J) (i : I) (h : X.obj i ⟶ Y.obj j)
    (hf : (finiteDiagramIndDualHomMap X Y f).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i
        (FintypeCat.Skeleton.incl.map h)) :
    (finiteDiagramIndDualPresheafMap X Y f).app
        (Opposite.op (Y.op.obj (Opposite.op j)))
        ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ (𝟙 _)) =
      (colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ h.op := by
  apply (finiteDiagramIndDualStageValueEquiv X (Y.obj j)).injective
  rw [finiteDiagramIndDualStageValueEquiv_apply,
    finiteDiagramIndDualStageValueEquiv_apply,
    finiteDiagramIndDualStageValue_ι X (Y.obj j) i h]
  simpa only [stageHomFunctor, stageHom, Functor.comp_obj, colim_obj,
    Functor.whiskeringLeft_obj_obj] using
    (finiteDiagramIndDualHomMap_apply X Y f j).symm.trans hf

private theorem finiteDiagramIndDualHomMap_apply_ι_of_class_at
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    (j : J) (i : I) (h : X.obj i ⟶ Y.obj j)
    (hf : (finiteDiagramIndDualHomMap X Y f).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i
        (FintypeCat.Skeleton.incl.map h))
    (s : FintypeCat.Skeleton.{u}) (k : Y.obj j ⟶ s) :
    (finiteDiagramIndDualPresheafMap X Y f).app (Opposite.op (Opposite.op s))
        ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ k.op) =
      (colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ (h ≫ k).op := by
  let η := finiteDiagramIndDualPresheafMap X Y f
  have hιY :
      ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ k.op) =
      (colimit (Y.op ⋙ yoneda)).map k.op.op
        ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ (𝟙 _)) := by
    simpa only [Functor.comp_obj, yoneda_obj_map, Quiver.Hom.unop_op,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
      CategoryTheory.comp_apply, Category.comp_id] using
      (types_congr_hom
        ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).naturality k.op.op) (𝟙 _))
  have hιX :
      ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ (h ≫ k).op) =
      (colimit (X.op ⋙ yoneda)).map k.op.op
        ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ h.op) := by
    simpa only [Functor.comp_obj, yoneda_obj_map, Quiver.Hom.unop_op,
      ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
      CategoryTheory.comp_apply, op_comp] using
      (types_congr_hom
        ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).naturality k.op.op) h.op)
  have hη :
      η.app _ ((colimit (Y.op ⋙ yoneda)).map k.op.op
        ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ (𝟙 _))) =
      (colimit (X.op ⋙ yoneda)).map k.op.op
        (η.app _ ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ (𝟙 _))) := by
    simpa only [CategoryTheory.comp_apply] using
      (types_congr_hom (η.naturality k.op.op)
        ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ (𝟙 _)))
  calc
    η.app _ ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ k.op) =
        η.app _ ((colimit (Y.op ⋙ yoneda)).map k.op.op
          ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ (𝟙 _))) :=
      congrArg _ hιY
    _ = (colimit (X.op ⋙ yoneda)).map k.op.op
          (η.app _ ((colimit.ι (Y.op ⋙ yoneda) (Opposite.op j)).app _ (𝟙 _))) := hη
    _ = (colimit (X.op ⋙ yoneda)).map k.op.op
          ((colimit.ι (X.op ⋙ yoneda) (Opposite.op i)).app _ h.op) :=
      congrArg _ (finiteDiagramIndDualHomMap_apply_ι_of_class X Y f j i h hf)
    _ = _ := hιX.symm

private theorem finiteDiagramIndDualHomMap_map
    {X X' : I ⥤ FintypeCat.Skeleton.{u}} (a : X ⟶ X') (i : I) :
    (finiteDiagramIndDualHomMap X X' (finiteDiagramIndDualMap a)).val i =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i
        (FintypeCat.Skeleton.incl.map (a.app i)) := by
  apply finiteDiagramIndDualHomMap_apply_class X X' _ i i (a.app i)
  rw [finiteDiagramIndDualPresheafMap_map]
  have hι := congrArg (fun η => η.app (Opposite.op (Opposite.op (X'.obj i))))
    (colimit.ι_map (Functor.whiskerRight (NatTrans.op a) yoneda) (Opposite.op i))
  have hp := types_congr_hom hι (𝟙 (Opposite.op (X'.obj i)))
  simpa only [colim_map, colim_obj, NatTrans.comp_app, CategoryTheory.comp_apply,
    Functor.whiskerRight_app, yoneda_map_app, Functor.comp_obj,
    Functor.op_obj, NatTrans.op_app,
    ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
    Category.id_comp] using hp

/-- Morphisms between the specified dual ind-objects correspond to compatible
classes of finite-stage maps.

This uses Mathlib’s `Ind` presentations and Yoneda colimits; the pro-category paragraph in
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1 motivates but does not
state this specified-diagram equivalence. -/
noncomputable def finiteDiagramIndDualHomEquiv
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u}) :
    (finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y) ≃
      ((Y ⋙ FintypeCat.Skeleton.incl) ⋙
        stageHomFunctor (X ⋙ FintypeCat.Skeleton.incl)).sections :=
  Equiv.ofBijective (finiteDiagramIndDualHomMap X Y) (by
    let H := Y.op.op ⋙ colimit (X.op ⋙ yoneda)
    constructor
    · intro f g heq
      apply (finiteDiagramIndDualPresheafMap_bijective X Y).1
      apply (colimitYonedaHomEquiv Y.op (colimit (X.op ⋙ yoneda))).injective
      apply Types.limit_ext
      intro j
      apply (finiteDiagramIndDualStageValueEquiv X (Y.obj j.unop.unop)).injective
      have hj := congrArg (fun sectionValue => sectionValue.val j.unop.unop) heq
      have hcoordinate := (finiteDiagramIndDualHomMap_apply X Y f j.unop.unop).symm.trans
        (hj.trans (finiteDiagramIndDualHomMap_apply X Y g j.unop.unop))
      dsimp only [H]
      rw [colimitYonedaHomEquiv_π_apply, colimitYonedaHomEquiv_π_apply]
      simpa only [finiteDiagramIndDualStageValueEquiv_apply, stageHomFunctor, stageHom,
        Functor.comp_obj, colim_obj, Functor.whiskeringLeft_obj_obj] using hcoordinate
    · intro sectionValue
      let coords : (j : Jᵒᵖᵒᵖ) → H.obj j := fun j =>
        (finiteDiagramIndDualStageValueEquiv X (Y.obj j.unop.unop)).symm
          (sectionValue.val j.unop.unop)
      have hcoords : ∀ (j k : Jᵒᵖᵒᵖ) (arrow : j ⟶ k),
          H.map arrow (coords j) = coords k := by
        intro j k arrow
        apply (finiteDiagramIndDualStageValueEquiv X (Y.obj k.unop.unop)).injective
        have hnat := finiteDiagramIndDualStageValue_naturality X
          (Y.map arrow.unop.unop) (coords j)
        change stageHomPost (F := X ⋙ FintypeCat.Skeleton.incl)
            (FintypeCat.Skeleton.incl.map (Y.map arrow.unop.unop))
            (finiteDiagramIndDualStageValue X (Y.obj j.unop.unop) (coords j)) =
          finiteDiagramIndDualStageValue X (Y.obj k.unop.unop)
            (H.map arrow (coords j)) at hnat
        have hs := sectionValue.property arrow.unop.unop
        change stageHomPost (F := X ⋙ FintypeCat.Skeleton.incl)
            (FintypeCat.Skeleton.incl.map (Y.map arrow.unop.unop))
            (sectionValue.val j.unop.unop) =
          sectionValue.val k.unop.unop at hs
        rw [finiteDiagramIndDualStageValueEquiv_apply, ← hnat,
          ← finiteDiagramIndDualStageValueEquiv_apply]
        dsimp only [coords]
        exact (congrArg (stageHomPost (F := X ⋙ FintypeCat.Skeleton.incl)
          (FintypeCat.Skeleton.incl.map (Y.map arrow.unop.unop)))
          ((finiteDiagramIndDualStageValueEquiv X
            (Y.obj j.unop.unop)).apply_symm_apply _)).trans
          (hs.trans ((finiteDiagramIndDualStageValueEquiv X
            (Y.obj k.unop.unop)).apply_symm_apply _).symm)
      let w := Types.Limit.mk H coords hcoords
      let η := (colimitYonedaHomEquiv Y.op (colimit (X.op ⋙ yoneda))).symm w
      obtain ⟨f, hf⟩ := (finiteDiagramIndDualPresheafMap_bijective X Y).2 η
      refine ⟨f, ?_⟩
      apply (Functor.sections_ext_iff).2
      intro j
      change finiteDiagramIndDualStageValue X (Y.obj j)
          (limit.π H (Opposite.op (Opposite.op j))
            (colimitYonedaHomEquiv Y.op (colimit (X.op ⋙ yoneda))
              (finiteDiagramIndDualPresheafMap X Y f))) = sectionValue.val j
      rw [hf]
      dsimp only [η]
      rw [Equiv.apply_symm_apply, show limit.π H (Opposite.op (Opposite.op j)) w =
        coords (Opposite.op (Opposite.op j)) from Types.Limit.π_mk H coords hcoords _]
      rw [← finiteDiagramIndDualStageValueEquiv_apply]
      exact (finiteDiagramIndDualStageValueEquiv X (Y.obj j)).apply_symm_apply _)

/-- The class at a later target stage is the postcomposition of the class at
an earlier stage, also for parallel target arrows. -/
theorem finiteDiagramIndDualHomMap_target_arrow
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    {j k : J} (a : j ⟶ k) :
    stageHomPost (F := X ⋙ FintypeCat.Skeleton.incl)
      (FintypeCat.Skeleton.incl.map (Y.map a))
      ((finiteDiagramIndDualHomMap X Y f).val j) =
        (finiteDiagramIndDualHomMap X Y f).val k :=
  (finiteDiagramIndDualHomMap X Y f).property a

/-- A dual ind-object morphism is determined by all its target-stage classes. -/
theorem finiteDiagramIndDualHomMap_ext
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    {f g : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y}
    (h : ∀ j, (finiteDiagramIndDualHomMap X Y f).val j =
      (finiteDiagramIndDualHomMap X Y g).val j) : f = g := by
  apply (finiteDiagramIndDualHomEquiv X Y).injective
  apply (Functor.sections_ext_iff).2
  exact h

/-- The inverse comparison recovers a chosen class at one target stage;
no simultaneous choice of source stage is required. -/
theorem finiteDiagramIndDualHomEquiv_symm_apply_class
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (x : ((Y ⋙ FintypeCat.Skeleton.incl) ⋙
      stageHomFunctor (X ⋙ FintypeCat.Skeleton.incl)).sections)
    (j : J) (i : I)
    (h : (X ⋙ FintypeCat.Skeleton.incl).obj i ⟶
      (Y ⋙ FintypeCat.Skeleton.incl).obj j)
    (hj : x.val j = stageHomClass (X ⋙ FintypeCat.Skeleton.incl)
      ((Y ⋙ FintypeCat.Skeleton.incl).obj j) i h) :
    (finiteDiagramIndDualHomMap X Y
      ((finiteDiagramIndDualHomEquiv X Y).symm x)).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl)
        ((Y ⋙ FintypeCat.Skeleton.incl).obj j) i h := by
  rw [← hj]
  exact congrArg (fun s => s.val j) ((finiteDiagramIndDualHomEquiv X Y).apply_symm_apply x)

/-- A second representative gives the same coordinate exactly when both maps
agree after one common source refinement. -/
theorem finiteDiagramIndDualHomMap_class_eq_iff
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y) (j : J)
    (i k : I)
    (h : (X ⋙ FintypeCat.Skeleton.incl).obj i ⟶
      (Y ⋙ FintypeCat.Skeleton.incl).obj j)
    (t : (X ⋙ FintypeCat.Skeleton.incl).obj k ⟶
      (Y ⋙ FintypeCat.Skeleton.incl).obj j)
    (hi : (finiteDiagramIndDualHomMap X Y f).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i h) :
    (finiteDiagramIndDualHomMap X Y f).val j =
        stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ k t ↔
      ∃ (l : I) (a : l ⟶ i) (b : l ⟶ k),
        (X ⋙ FintypeCat.Skeleton.incl).map a ≫ h =
          (X ⋙ FintypeCat.Skeleton.incl).map b ≫ t := by
  rw [hi]
  exact stageHomClass_eq_iff (X ⋙ FintypeCat.Skeleton.incl) _ i k h t

/-- The identity's coordinate is the identity on its target stage. -/
theorem finiteDiagramIndDualHomMap_id
    (X : I ⥤ FintypeCat.Skeleton.{u}) (i : I) :
    (finiteDiagramIndDualHomMap X X (𝟙 (finiteDiagramIndDual X))).val i =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl)
        ((X ⋙ FintypeCat.Skeleton.incl).obj i) i (𝟙 _) := by
  apply finiteDiagramIndDualHomMap_apply_class X X _ i i (𝟙 _)
  rw [finiteDiagramIndDualPresheafMap_id]
  simp only [NatTrans.id_app, CategoryTheory.id_apply, op_id]
  rfl

/-- Composition transports representatives by composing stage maps. This is
a compatibility statement for the comparison, not a new category law. -/
theorem finiteDiagramIndDualHomMap_comp_class
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (Z : K ⥤ FintypeCat.Skeleton.{u})
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    (g : finiteDiagramIndDual Y ⟶ finiteDiagramIndDual Z)
    (i : I) (j : J) (k : K)
    (h : (X ⋙ FintypeCat.Skeleton.incl).obj i ⟶
      (Y ⋙ FintypeCat.Skeleton.incl).obj j)
    (t : (Y ⋙ FintypeCat.Skeleton.incl).obj j ⟶
      (Z ⋙ FintypeCat.Skeleton.incl).obj k)
    (hf : (finiteDiagramIndDualHomMap X Y f).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i h)
    (hg : (finiteDiagramIndDualHomMap Y Z g).val k =
      stageHomClass (Y ⋙ FintypeCat.Skeleton.incl) _ j t) :
    (finiteDiagramIndDualHomMap X Z (f ≫ g)).val k =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i (h ≫ t) := by
  obtain ⟨h₀, rfl⟩ := (FintypeCat.Skeleton.incl).map_surjective h
  obtain ⟨t₀, rfl⟩ := (FintypeCat.Skeleton.incl).map_surjective t
  rw [← Functor.map_comp]
  apply finiteDiagramIndDualHomMap_apply_class X Z _ k i (h₀ ≫ t₀)
  rw [finiteDiagramIndDualPresheafMap_comp]
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply]
  rw [finiteDiagramIndDualHomMap_apply_ι_of_class Y Z g k j t₀ hg]
  exact finiteDiagramIndDualHomMap_apply_ι_of_class_at X Y f j i h₀ hf
    (Z.obj k) t₀

/-- Precomposition by a fixed-index source diagram map acts at the chosen
source stage, without changing the target coordinate. -/
theorem finiteDiagramIndDualHomMap_source_naturality
    (X' X : I ⥤ FintypeCat.Skeleton.{u})
    (Y : J ⥤ FintypeCat.Skeleton.{u}) (a : X' ⟶ X)
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    (i : I) (j : J)
    (h : (X ⋙ FintypeCat.Skeleton.incl).obj i ⟶
      (Y ⋙ FintypeCat.Skeleton.incl).obj j)
    (hf : (finiteDiagramIndDualHomMap X Y f).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i h) :
    (finiteDiagramIndDualHomMap X' Y (finiteDiagramIndDualMap a ≫ f)).val j =
      stageHomClass (X' ⋙ FintypeCat.Skeleton.incl) _ i
        (FintypeCat.Skeleton.incl.map (a.app i) ≫ h) := by
  exact finiteDiagramIndDualHomMap_comp_class X' X Y (finiteDiagramIndDualMap a) f
    i i j (FintypeCat.Skeleton.incl.map (a.app i)) h
    (finiteDiagramIndDualHomMap_map a i) hf

/-- Postcomposition by a fixed-index target diagram map acts at the same
target stage. -/
theorem finiteDiagramIndDualHomMap_target_naturality
    (X : I ⥤ FintypeCat.Skeleton.{u})
    (Y Y' : J ⥤ FintypeCat.Skeleton.{u}) (a : Y ⟶ Y')
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    (i : I) (j : J)
    (h : (X ⋙ FintypeCat.Skeleton.incl).obj i ⟶
      (Y ⋙ FintypeCat.Skeleton.incl).obj j)
    (hf : (finiteDiagramIndDualHomMap X Y f).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i h) :
    (finiteDiagramIndDualHomMap X Y' (f ≫ finiteDiagramIndDualMap a)).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i
        (h ≫ FintypeCat.Skeleton.incl.map (a.app j)) := by
  exact finiteDiagramIndDualHomMap_comp_class X Y Y' f (finiteDiagramIndDualMap a)
    i j j h (FintypeCat.Skeleton.incl.map (a.app j)) hf
    (finiteDiagramIndDualHomMap_map a j)

/-- Apply the class comparison to continuous maps between specified limiting
finite-space cones. -/
noncomputable def finiteDiagramIndDualContinuousEquiv
    (X : I ⥤ FintypeCat.Skeleton.{u})
    (Y : J ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d) :
    (finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y) ≃ (c.pt ⟶ d.pt) :=
  (finiteDiagramIndDualHomEquiv X Y).trans
    (stageHomLimitEquiv (X ⋙ FintypeCat.Skeleton.incl) c hc
      (Y ⋙ FintypeCat.Skeleton.incl) d hd).symm

/-- On maps out of a dual ind-object, the continuous comparison is the
inverse of the finite-cone stage-hom comparison. -/
@[simp]
theorem finiteDiagramIndDualContinuousEquiv_apply
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d)
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y) :
    finiteDiagramIndDualContinuousEquiv X Y c hc d hd f =
      (stageHomLimitEquiv (X ⋙ FintypeCat.Skeleton.incl) c hc
        (Y ⋙ FintypeCat.Skeleton.incl) d hd).symm
          (finiteDiagramIndDualHomMap X Y f) := rfl

/-- In the inverse direction, the class at each target stage is the class
of the corresponding composite with the target projection. -/
theorem finiteDiagramIndDualContinuousEquiv_symm_apply_projection
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d)
    (g : c.pt ⟶ d.pt) (j : J) :
    (finiteDiagramIndDualHomMap X Y
      ((finiteDiagramIndDualContinuousEquiv X Y c hc d hd).symm g)).val j =
      (stageHomLimitMap (X ⋙ FintypeCat.Skeleton.incl) c hc
        (Y ⋙ FintypeCat.Skeleton.incl) d g).val j := by
  have hsections :
      finiteDiagramIndDualHomMap X Y
        ((finiteDiagramIndDualContinuousEquiv X Y c hc d hd).symm g) =
      stageHomLimitEquiv (X ⋙ FintypeCat.Skeleton.incl) c hc
        (Y ⋙ FintypeCat.Skeleton.incl) d hd g := by
    apply (stageHomLimitEquiv (X ⋙ FintypeCat.Skeleton.incl) c hc
      (Y ⋙ FintypeCat.Skeleton.incl) d hd).symm.injective
    calc
      _ = g := by
        simpa only [finiteDiagramIndDualContinuousEquiv_apply] using
          (finiteDiagramIndDualContinuousEquiv X Y c hc d hd).apply_symm_apply g
      _ = _ := ((stageHomLimitEquiv (X ⋙ FintypeCat.Skeleton.incl) c hc
        (Y ⋙ FintypeCat.Skeleton.incl) d hd).symm_apply_apply g).symm
  simpa only [stageHomLimitEquiv_apply] using
    congrArg (fun sectionValue => sectionValue.val j) hsections

/-- The continuous map's composite with a target projection is represented
by any chosen source-stage representative of that target class. -/
theorem finiteDiagramIndDualContinuousEquiv_apply_class
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d)
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    (j : J) (i : I)
    (h : (X ⋙ FintypeCat.Skeleton.incl).obj i ⟶
      (Y ⋙ FintypeCat.Skeleton.incl).obj j)
    (hj : (finiteDiagramIndDualHomMap X Y f).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i h) :
    finiteDiagramIndDualContinuousEquiv X Y c hc d hd f ≫ d.π.app j =
      c.π.app i ≫ FintypeCat.toProfinite.map h := by
  exact stageHomLimitEquiv_symm_apply_class
    (X ⋙ FintypeCat.Skeleton.incl) c hc
      (Y ⋙ FintypeCat.Skeleton.incl) d hd _ j i h hj

/-- The continuous comparison sends the identity on a dual finite diagram
to the identity of its specified limit. -/
@[simp] theorem finiteDiagramIndDualContinuousEquiv_id
    (X : I ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c) :
    finiteDiagramIndDualContinuousEquiv X X c hc c hc
      (𝟙 (finiteDiagramIndDual X)) = 𝟙 c.pt := by
  apply hc.hom_ext
  intro i
  rw [finiteDiagramIndDualContinuousEquiv_apply_class X X c hc c hc
    (𝟙 _) i i (𝟙 _) (finiteDiagramIndDualHomMap_id X i)]
  simp

/-- The continuous comparison preserves composition across specified
limits of three finite diagrams. -/
theorem finiteDiagramIndDualContinuousEquiv_comp
    (X : I ⥤ FintypeCat.Skeleton.{u}) (Y : J ⥤ FintypeCat.Skeleton.{u})
    (Z : K ⥤ FintypeCat.Skeleton.{u})
    (c : Cone ((X ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hc : IsLimit c)
    (d : Cone ((Y ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (hd : IsLimit d)
    (e : Cone ((Z ⋙ FintypeCat.Skeleton.incl) ⋙ FintypeCat.toProfinite))
    (he : IsLimit e)
    (f : finiteDiagramIndDual X ⟶ finiteDiagramIndDual Y)
    (g : finiteDiagramIndDual Y ⟶ finiteDiagramIndDual Z) :
    finiteDiagramIndDualContinuousEquiv X Z c hc e he (f ≫ g) =
      finiteDiagramIndDualContinuousEquiv X Y c hc d hd f ≫
        finiteDiagramIndDualContinuousEquiv Y Z d hd e he g := by
  apply he.hom_ext
  intro k
  obtain ⟨⟨j⟩, t, ht⟩ := Limits.Types.jointly_surjective'
    (F := stageHom (Y ⋙ FintypeCat.Skeleton.incl)
      ((Z ⋙ FintypeCat.Skeleton.incl).obj k))
    ((finiteDiagramIndDualHomMap Y Z g).val k)
  change (Y ⋙ FintypeCat.Skeleton.incl).obj j ⟶
    (Z ⋙ FintypeCat.Skeleton.incl).obj k at t
  have ht' : (finiteDiagramIndDualHomMap Y Z g).val k =
      stageHomClass (Y ⋙ FintypeCat.Skeleton.incl) _ j t := ht.symm
  obtain ⟨⟨i⟩, h, hh⟩ := Limits.Types.jointly_surjective'
    (F := stageHom (X ⋙ FintypeCat.Skeleton.incl)
      ((Y ⋙ FintypeCat.Skeleton.incl).obj j))
    ((finiteDiagramIndDualHomMap X Y f).val j)
  change (X ⋙ FintypeCat.Skeleton.incl).obj i ⟶
    (Y ⋙ FintypeCat.Skeleton.incl).obj j at h
  have hh' : (finiteDiagramIndDualHomMap X Y f).val j =
      stageHomClass (X ⋙ FintypeCat.Skeleton.incl) _ i h := hh.symm
  calc
    _ = c.π.app i ≫ FintypeCat.toProfinite.map (h ≫ t) :=
      finiteDiagramIndDualContinuousEquiv_apply_class X Z c hc e he (f ≫ g)
        k i (h ≫ t)
        (finiteDiagramIndDualHomMap_comp_class X Y Z f g i j k h t hh' ht')
    _ = _ := by
      rw [Functor.map_comp, ← Category.assoc,
        ← finiteDiagramIndDualContinuousEquiv_apply_class X Y c hc d hd f j i h hh',
        Category.assoc,
        ← finiteDiagramIndDualContinuousEquiv_apply_class Y Z d hd e he g k j t ht',
        Category.assoc]

end Profinite
