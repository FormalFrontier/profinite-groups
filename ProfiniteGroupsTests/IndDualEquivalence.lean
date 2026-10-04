/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.IndDualEquivalence

/-!
# Quotient-presentation clients

The empty space has empty finite quotients. The two-point space has a quotient
that distinguishes its points. An infinite binary product also has distinct
points detected by a finite quotient. These calculations are independent of
the equivalence's inverse laws; the subsequent examples use the skeletal cone
and its realization comparison on the same concrete spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits FintypeCat Profinite

set_option warningAsError true

namespace ProfiniteGroupsTests.IndDualEquivalence

private abbrev emptySpace : Profinite := Profinite.of PEmpty

/-- Every finite quotient of the empty space is empty. -/
example (S : DiscreteQuotient emptySpace) : IsEmpty S := by
  constructor
  intro s
  obtain ⟨p, _⟩ := S.proj_surjective s
  exact p.elim

/-- Its skeletal quotient cone still has the original empty space as point. -/
example : (skeletalQuotientCone emptySpace).pt = emptySpace :=
  skeletalQuotientCone_pt _

private abbrev twoSpace : Profinite := Profinite.of (Fin 2)

/-- The finest discrete quotient detects the two different finite points. -/
private theorem two_points_separated :
    (⊥ : DiscreteQuotient twoSpace).proj (0 : Fin 2) ≠
      (⊥ : DiscreteQuotient twoSpace).proj (1 : Fin 2) := by
  intro h
  have heq := DiscreteQuotient.proj_bot_injective h
  exact (by decide : (0 : Fin 2) ≠ 1) heq

/-- The concrete two-point object has a realized skeletal quotient presentation. -/
noncomputable example : indDualRealization.obj (skeletalQuotientIndDual twoSpace) ≅ twoSpace :=
  skeletalQuotientRealizationIso _

/-- The profinite space of infinite binary sequences. -/
abbrev binarySpace : Profinite := Profinite.of (ℕ → Fin 2)

private def binaryZero : ℕ → Fin 2 := fun _ => 0

private def binaryOne : ℕ → Fin 2 := fun n => if n = 0 then 1 else 0

private def binarySpike (n : ℕ) : ℕ → Fin 2 := fun m => if m = n then 1 else 0

/-- Binary sequences form an infinite profinite space. -/
private theorem binary_space_infinite : Infinite binarySpace := by
  apply Infinite.of_injective binarySpike
  intro m n h
  by_contra hmn
  have hvalue := congrArg (fun b : binarySpace => b m) h
  simp [binarySpike, hmn] at hvalue

/-- The infinite binary product has two explicitly different compatible points. -/
private theorem binary_points_ne : binaryZero ≠ binaryOne := by
  intro h
  have heq := congrArg (fun b : binarySpace => b 0) h
  simp [binaryZero, binaryOne] at heq

/-- Some finite quotient of the infinite binary product separates the two points. -/
private theorem binary_quotient_separates :
    ∃ S : DiscreteQuotient binarySpace,
      S.proj binaryZero ≠ S.proj binaryOne := by
  by_contra h
  push Not at h
  exact binary_points_ne (DiscreteQuotient.eq_of_forall_proj_eq h)

/-- The binary product's concrete model is compared with the generic inverse
without identifying their chosen dual ind-objects definitionally. -/
noncomputable example : indDualEquivalence.inverse.obj binarySpace ≅
    skeletalQuotientIndDual binarySpace :=
  indDualEquivalenceInverseIso _

/-- On the binary product, skeletal projections are the quotient projections
transported by the inverse counit, also at a quotient separating two points. -/
example : ∃ S : DiscreteQuotient binarySpace,
    S.proj binaryZero ≠ S.proj binaryOne ∧
    (skeletalQuotientCone binarySpace).π.app S =
      binarySpace.asLimitCone.π.app S ≫
        FintypeCat.toProfinite.map
          (FintypeCat.Skeleton.equivalence.counitIso.inv.app
            (binarySpace.fintypeDiagram.obj S)) := by
  obtain ⟨S, h⟩ := binary_quotient_separates
  exact ⟨S, h, skeletalQuotientCone_π _ S⟩

/-- The explicit binary sequence with a first bit uses the finite
quotient of its coordinates, not a chosen inverse presentation. -/
example (S : DiscreteQuotient binarySpace) :
    (skeletalQuotientCone binarySpace).π.app S binaryOne =
      (FintypeCat.Skeleton.equivalence.counitIso.inv.app
        (binarySpace.fintypeDiagram.obj S)) (S.proj binaryOne) :=
  skeletalQuotientCone_π_apply _ S _

end ProfiniteGroupsTests.IndDualEquivalence
