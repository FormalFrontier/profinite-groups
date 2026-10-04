/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Category.Profinite.Extend
public import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Images of finite stages in cofiltered limits

The image of a projection from a limiting cone of finite discrete spaces is
already the image of one finite-stage transition. Consequently, equality of
maps to an arbitrary type can be checked after a finite refinement. The
statements allow empty stages and do not require surjective projections.

The index is small, and stages and the limiting profinite space live in
`max u w`: this is the universe of Mathlib's explicit `Profinite.limitCone`
for an index in `Type u` and finite stages in `FintypeCat.{max u w}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat

universe u w v

namespace Profinite

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    {F : I ⥤ FintypeCat.{max u w}} (c : Cone (F ⋙ FintypeCat.toProfinite))

/-- The image of a projection of a finite-discrete limit is the eventual range
of the underlying finite-set diagram. -/
theorem range_π_eq_eventualRange (hc : IsLimit c) (i : I) :
    Set.range (c.π.app i : c.pt → F.obj i) =
      (F ⋙ FintypeCat.incl).eventualRange i := by
  let D : I ⥤ Type (max u w) := F ⋙ FintypeCat.incl
  have : ∀ j : I, Finite (D.obj j) := fun j => by
    change Finite (F.obj j)
    infer_instance
  have hML : D.IsMittagLeffler :=
    D.isMittagLeffler_of_exists_finite_range
      (fun j => ⟨j, 𝟙 j, Set.toFinite _⟩)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply D.mem_eventualRange_iff.2
    intro j f
    refine ⟨c.π.app j y, ?_⟩
    have hw := congrArg (fun p : c.pt ⟶ (F ⋙ FintypeCat.toProfinite).obj i => p y)
      (c.w f)
    change F.map f (c.π.app j y) = c.π.app i y at hw
    exact hw
  · intro hx
    have hNonempty : ∀ j : I, Nonempty (D.toEventualRanges.obj j) := by
      intro j
      obtain ⟨k, a, b, _⟩ := IsCofilteredOrEmpty.cone_objs i j
      obtain ⟨z, hz, _⟩ := hML.subset_image_eventualRange D a hx
      exact ⟨⟨D.map b z, D.eventualRange_mapsTo b hz⟩⟩
    have : ∀ j : I, Nonempty (D.toEventualRanges.obj j) := hNonempty
    have hSurj : ∀ ⦃j k : I⦄ (f : j ⟶ k),
        Function.Surjective (D.toEventualRanges.map f) :=
      fun _ _ f => D.surjective_toEventualRanges hML f
    obtain ⟨s, hs⟩ :=
      D.toEventualRanges.eval_section_surjective_of_surjective hSurj i ⟨x, hx⟩
    let t : D.sections := D.toEventualRangesSectionsEquiv s
    have ht : t.val i = x := congrArg Subtype.val hs
    let y : (limitCone (F ⋙ FintypeCat.toProfinite)).pt :=
      ⟨t.val, fun {j k} f => by
        change F.map f (t.val j) = t.val k
        exact t.prop f⟩
    refine ⟨hc.lift (limitCone (F ⋙ FintypeCat.toProfinite)) y, ?_⟩
    have hf := congrArg
      (fun p : (limitCone (F ⋙ FintypeCat.toProfinite)).pt ⟶
        (F ⋙ FintypeCat.toProfinite).obj i => p y)
      (hc.fac (limitCone (F ⋙ FintypeCat.toProfinite)) i)
    have hy : (limitCone (F ⋙ FintypeCat.toProfinite)).π.app i y = t.val i := rfl
    exact (hf.trans hy).trans ht

/-- The image of a projection from a finite-discrete limit stabilizes at one
transition, including when that image is empty. -/
theorem exists_stage_range_eq (hc : IsLimit c) (i : I) :
    ∃ (j : I) (a : j ⟶ i),
      Set.range (c.π.app i : c.pt → F.obj i) = Set.range (F.map a : F.obj j → F.obj i) := by
  let D : I ⥤ Type (max u w) := F ⋙ FintypeCat.incl
  have : ∀ j : I, Finite (D.obj j) := fun j => by
    change Finite (F.obj j)
    infer_instance
  have hML : D.IsMittagLeffler :=
    D.isMittagLeffler_of_exists_finite_range
      (fun j => ⟨j, 𝟙 j, Set.toFinite _⟩)
  obtain ⟨j, a, ha⟩ := (D.isMittagLeffler_iff_eventualRange).1 hML i
  exact ⟨j, a, (range_π_eq_eventualRange c hc i).trans ha⟩

/-- Maps out of one finite stage that agree on the limit agree after a
refinement. The target need not be finite or topological. -/
theorem exists_stage_map_eq_of_limit_eq (hc : IsLimit c) {S : Type v} (i : I)
    (h g : F.obj i → S)
    (heq : ∀ x : c.pt, h (c.π.app i x) = g (c.π.app i x)) :
    ∃ (j : I) (a : j ⟶ i), ∀ x : F.obj j, h (F.map a x) = g (F.map a x) := by
  obtain ⟨j, a, ha⟩ := exists_stage_range_eq c hc i
  refine ⟨j, a, fun x => ?_⟩
  obtain ⟨y, hy⟩ : F.map a x ∈ Set.range (c.π.app i : c.pt → F.obj i) := by
    rw [ha]
    exact ⟨x, rfl⟩
  rw [← hy]
  exact heq y

/-- Maps out of different finite stages that agree on the limit agree after
one common refinement. -/
theorem exists_common_stage_map_eq_of_limit_eq (hc : IsLimit c) {S : Type v}
    (i k : I) (h : F.obj i → S) (g : F.obj k → S)
    (heq : ∀ x : c.pt, h (c.π.app i x) = g (c.π.app k x)) :
    ∃ (j : I) (a : j ⟶ i) (b : j ⟶ k),
      ∀ x : F.obj j, h (F.map a x) = g (F.map b x) := by
  obtain ⟨j, a, b, _⟩ := IsCofilteredOrEmpty.cone_objs i k
  have heq' : ∀ x : c.pt,
      (h ∘ F.map a) (c.π.app j x) = (g ∘ F.map b) (c.π.app j x) := by
    intro x
    have ha := congrArg
      (fun p : c.pt ⟶ (F ⋙ FintypeCat.toProfinite).obj i => p x) (c.w a)
    have hb := congrArg
      (fun p : c.pt ⟶ (F ⋙ FintypeCat.toProfinite).obj k => p x) (c.w b)
    change F.map a (c.π.app j x) = c.π.app i x at ha
    change F.map b (c.π.app j x) = c.π.app k x at hb
    change h (F.map a (c.π.app j x)) = g (F.map b (c.π.app j x))
    rw [ha, hb]
    exact heq x
  obtain ⟨l, f, hf⟩ :=
    exists_stage_map_eq_of_limit_eq c hc j (h ∘ F.map a) (g ∘ F.map b) heq'
  refine ⟨l, f ≫ a, f ≫ b, fun x => ?_⟩
  simpa only [F.map_comp, FintypeCat.comp_apply, Function.comp_apply] using hf x

/-- If a cofiltered limit of finite discrete spaces is empty, then one of its
finite stages is empty. No stage-inhabitedness assumption is needed. -/
theorem exists_isEmpty_stage_of_isEmpty_limit (hc : IsLimit c) [IsEmpty c.pt] :
    ∃ j : I, IsEmpty (F.obj j) := by
  let i : I := Classical.choice IsCofiltered.nonempty
  obtain ⟨j, a, ha⟩ := exists_stage_range_eq c hc i
  refine ⟨j, ⟨fun x => ?_⟩⟩
  obtain ⟨y, _⟩ : F.map a x ∈ Set.range (c.π.app i : c.pt → F.obj i) := by
    rw [ha]
    exact ⟨x, rfl⟩
  have noPoint : IsEmpty c.pt := inferInstance
  exact (noPoint.false y).elim

end Profinite
