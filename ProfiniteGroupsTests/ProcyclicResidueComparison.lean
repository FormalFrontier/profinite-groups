/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroupsTests.ProcyclicResidueDiagram

/-!
# Generator-normalized residue-comparison clients

These applications use the chosen-generator natural comparison at two pro-2
levels, their nonidentity reduction arrow, and the supported reconstruction.
The residue-diagram client module contains the definition-only boundary cases.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProcyclicPowerLimitTests

universe u

namespace ProcyclicResidueComparisonTests

local instance : IsMulCommutative twoPrimary.{u} :=
  twoPrimary_isProcyclic.{u}.isMulCommutative

/-- One fixed generator identifies residue one with its power class at two
different supported levels of a torsion-free pro-2 group. -/
theorem two_primary_same_generator (g : twoPrimary.{u})
    (hg : IsTopologicalGenerator twoPrimary.{u} g) :
    (residuePowerQuotientNatIsoOfInfiniteSupport twoPrimary.{u}
      twoPrimary_isProcyclic.{u} g hg
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤} (Set.Subset.rfl)).hom.app
        indexTwo.{u} (ULift.up (Multiplicative.ofAdd
          (1 : ZMod (indexTwo.{u}).val))) =
          QuotientGroup.mk' (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 2 :
            Subgroup twoPrimary.{u}) g ∧
    (residuePowerQuotientNatIsoOfInfiniteSupport twoPrimary.{u}
      twoPrimary_isProcyclic.{u} g hg
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤} (Set.Subset.rfl)).hom.app
        indexFour.{u} (ULift.up (Multiplicative.ofAdd
          (1 : ZMod (indexFour.{u}).val))) =
          QuotientGroup.mk' (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 4 :
            Subgroup twoPrimary.{u}) g := by
  constructor
  · exact residuePowerQuotientComponent_hom_one twoPrimary.{u}
      twoPrimary_isProcyclic.{u} g hg indexTwo.{u}
      (powerImage_index_eq_of_infiniteSupport twoPrimary.{u}
        twoPrimary_isProcyclic.{u} _ Set.Subset.rfl indexTwo.{u})
  · exact residuePowerQuotientComponent_hom_one twoPrimary.{u}
      twoPrimary_isProcyclic.{u} g hg indexFour.{u}
      (powerImage_index_eq_of_infiniteSupport twoPrimary.{u}
        twoPrimary_isProcyclic.{u} _ Set.Subset.rfl indexFour.{u})

/-- For one fixed generator, the comparison at residue three commutes with
the nonidentity arrow from the fourth-power stage to the second-power stage. -/
theorem two_primary_four_to_two_comparison (g : twoPrimary.{u})
    (hg : IsTopologicalGenerator twoPrimary.{u} g) :
    (powerQuotientDiagram twoPrimary.{u} twoPrimary_isProcyclic.{u}
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).map
        (homOfLE (show indexFour.{u} ≤ indexTwo.{u} by
          apply (Nat.PowerIndex.le_iff _ _).mpr
          decide))
        ((residuePowerQuotientNatIso twoPrimary.{u} twoPrimary_isProcyclic.{u} g hg
          {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}
          (powerImage_index_eq_of_infiniteSupport twoPrimary.{u}
            twoPrimary_isProcyclic.{u} _ Set.Subset.rfl)).hom.app indexFour.{u}
          (ULift.up (Multiplicative.ofAdd (3 : ZMod 4)))) =
      (residuePowerQuotientNatIso twoPrimary.{u} twoPrimary_isProcyclic.{u} g hg
        {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}
        (powerImage_index_eq_of_infiniteSupport twoPrimary.{u}
          twoPrimary_isProcyclic.{u} _ Set.Subset.rfl)).hom.app indexTwo.{u}
        (ULift.up (Multiplicative.ofAdd (1 : ZMod 2))) := by
  have hreduce :
      (residueDiagram.{u}
        {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).map
          (homOfLE (show indexFour.{u} ≤ indexTwo.{u} by
            apply (Nat.PowerIndex.le_iff _ _).mpr
            decide))
          (ULift.up (Multiplicative.ofAdd (3 : ZMod (indexFour.{u}).val))) =
        ULift.up (Multiplicative.ofAdd (1 : ZMod (indexTwo.{u}).val)) :=
    ProcyclicResidueDiagramTests.two_primary_four_to_two_residue.{u}
  have hnat := residuePowerQuotientNatIso_naturality_apply twoPrimary.{u}
    twoPrimary_isProcyclic.{u} g hg
    {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}
    (powerImage_index_eq_of_infiniteSupport twoPrimary.{u}
      twoPrimary_isProcyclic.{u} _ Set.Subset.rfl)
    (homOfLE (show indexFour.{u} ≤ indexTwo.{u} by
      apply (Nat.PowerIndex.le_iff _ _).mpr
      decide)) (3 : ZMod (indexFour.{u}).val)
  rw [hreduce] at hnat
  exact hnat

/-- The nontrivial pro-2 realization sends its fixed generator to one
modulo four under the supported reconstruction. -/
theorem two_primary_generator_four :
    (continuousMulEquivSupportedResidueLimit twoPrimary.{u}
      twoPrimary_isProcyclic.{u} twoPrimary_isMulTorsionFree.{u}
      (primewisePadicRealizationGenerator twoPrimaryExponents)
      (primewisePadicRealizationGenerator_isTopologicalGenerator twoPrimaryExponents)
      (primewisePadicRealizationGenerator twoPrimaryExponents)).val indexFour.{u} =
        ULift.up (Multiplicative.ofAdd (1 : ZMod 4)) := by
  exact continuousMulEquivSupportedResidueLimit_generator _ _ _ _ _ _

end ProcyclicResidueComparisonTests
