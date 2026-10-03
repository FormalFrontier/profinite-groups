/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicPowerTransition
public import ProfiniteGroupsTests.ProcyclicPowerIndex

/-!
# Clients for procyclic power-quotient transitions

The order-twelve cyclic group realizes a nontrivial transition of exact
indices twelve to four. Maps are also available at levels with smaller
indices, as shown by the order-two group's fourth-power quotient.
-/

@[expose] public section

open ProfiniteGrp

namespace ProcyclicPowerTransitionTests

/-- The twelfth powers in the order-twelve cyclic group have index twelve. -/
theorem twelve_twelfth_index :
    (powerImage (finiteCyclic 12) (finiteCyclic_isProcyclic 12) 12 :
      Subgroup (finiteCyclic 12)).index = 12 := by
  apply (powerImage_index_eq_iff_exponents _ _ 12 (by decide)).mpr
  intro p
  rw [finiteCyclic_exponents_eq_factorization 12 p]

/-- The fourth powers in the order-twelve cyclic group have index four. -/
theorem twelve_fourth_index :
    (powerImage (finiteCyclic 12) (finiteCyclic_isProcyclic 12) 4 :
      Subgroup (finiteCyclic 12)).index = 4 :=
  powerImage_index_eq_of_dvd _ _ (by decide : 4 ∣ 12) (by decide) twelve_twelfth_index

/-- Reduction between exact cyclic quotients preserves the chosen generator. -/
theorem twelve_to_four_generator :
    powerImage_quotientMap (finiteCyclic 12) (finiteCyclic_isProcyclic 12)
      (by decide : 4 ∣ 12)
      ((powerImage_zmodContinuousMulEquiv (finiteCyclic 12)
        (finiteCyclic_isProcyclic 12) (finiteCyclicGenerator 12)
        (finiteCyclicGenerator_isTopologicalGenerator 12) 12 (by decide)
        twelve_twelfth_index) (Multiplicative.ofAdd (1 : ZMod 12))) =
    (powerImage_zmodContinuousMulEquiv (finiteCyclic 12)
      (finiteCyclic_isProcyclic 12) (finiteCyclicGenerator 12)
      (finiteCyclicGenerator_isTopologicalGenerator 12) 4 (by decide)
      twelve_fourth_index) (Multiplicative.ofAdd (1 : ZMod 4)) := by
  simp

/-- Reduction sends a non-generator residue to its class modulo four. -/
theorem twelve_to_four_six :
    powerImage_quotientMap (finiteCyclic 12) (finiteCyclic_isProcyclic 12)
      (by decide : 4 ∣ 12)
      ((powerImage_zmodContinuousMulEquiv (finiteCyclic 12)
        (finiteCyclic_isProcyclic 12) (finiteCyclicGenerator 12)
        (finiteCyclicGenerator_isTopologicalGenerator 12) 12 (by decide)
        twelve_twelfth_index) (Multiplicative.ofAdd (6 : ZMod 12))) =
    (powerImage_zmodContinuousMulEquiv (finiteCyclic 12)
      (finiteCyclic_isProcyclic 12) (finiteCyclicGenerator 12)
      (finiteCyclicGenerator_isTopologicalGenerator 12) 4 (by decide)
      twelve_fourth_index) (Multiplicative.ofAdd (2 : ZMod 4)) := by
  simpa only [map_ofNat, show (6 : ZMod 4) = 2 by decide] using
    (powerImage_quotientMap_zmod (finiteCyclic 12)
      (finiteCyclic_isProcyclic 12) (finiteCyclicGenerator 12)
      (finiteCyclicGenerator_isTopologicalGenerator 12) (by decide : 4 ∣ 12)
      (by decide) twelve_twelfth_index (6 : ZMod 12))

/-- The order-twelve to order-four transition hits its nonidentity
generator and is onto. -/
theorem twelve_to_four_surjective_nontrivial :
    Function.Surjective (powerImage_quotientMap (finiteCyclic 12)
      (finiteCyclic_isProcyclic 12) (by decide : 4 ∣ 12)) ∧
      powerImage_quotientMap (finiteCyclic 12) (finiteCyclic_isProcyclic 12)
        (by decide : 4 ∣ 12)
        (QuotientGroup.mk' (powerImage (finiteCyclic 12)
          (finiteCyclic_isProcyclic 12) 12 : Subgroup (finiteCyclic 12))
          (finiteCyclicGenerator 12)) ≠ 1 := by
  refine ⟨powerImage_quotientMap_surjective _ _ (by decide : 4 ∣ 12), ?_⟩
  rw [powerImage_quotientMap_apply_mk]
  intro heq
  have hgen := powerImage_zmodContinuousMulEquiv_symm_apply_generator
    (finiteCyclic 12) (finiteCyclic_isProcyclic 12) (finiteCyclicGenerator 12)
    (finiteCyclicGenerator_isTopologicalGenerator 12) 4 (by decide)
    twelve_fourth_index
  rw [heq] at hgen
  exact (by decide : Multiplicative.ofAdd (1 : ZMod 4) ≠ 1)
    (by simpa only [map_one] using hgen.symm)

/-- The zero-power quotient still maps onto a nontrivial fourth-power quotient. -/
theorem twelve_zero_to_four_nontrivial :
    powerImage_quotientMap (finiteCyclic 12) (finiteCyclic_isProcyclic 12)
      (dvd_zero 4)
      (QuotientGroup.mk' (powerImage (finiteCyclic 12)
        (finiteCyclic_isProcyclic 12) 0 : Subgroup (finiteCyclic 12))
        (finiteCyclicGenerator 12)) ≠ 1 := by
  have hnontrivial := twelve_to_four_surjective_nontrivial.2
  rw [powerImage_quotientMap_apply_mk] at hnontrivial ⊢
  exact hnontrivial

/-- At level one the quotient transition collapses every generator class. -/
theorem twelve_to_one_generator :
    powerImage_quotientMap (finiteCyclic 12) (finiteCyclic_isProcyclic 12)
      (by decide : 1 ∣ 12)
      (QuotientGroup.mk' (powerImage (finiteCyclic 12)
        (finiteCyclic_isProcyclic 12) 12 : Subgroup (finiteCyclic 12))
        (finiteCyclicGenerator 12)) = 1 := by
  rw [powerImage_quotientMap_apply_mk]
  apply (QuotientGroup.eq_one_iff (finiteCyclicGenerator 12)).mpr
  exact (mem_powerImage_iff _ _ 1 _).mpr
    ⟨finiteCyclicGenerator 12, by simp⟩

/-- Identity transition at a nontrivial quotient preserves its generator. -/
theorem twelve_identity_generator :
    powerImage_quotientMap (finiteCyclic 12) (finiteCyclic_isProcyclic 12)
      (dvd_refl 12)
      (QuotientGroup.mk' (powerImage (finiteCyclic 12)
        (finiteCyclic_isProcyclic 12) 12 : Subgroup (finiteCyclic 12))
        (finiteCyclicGenerator 12)) =
    QuotientGroup.mk' (powerImage (finiteCyclic 12)
      (finiteCyclic_isProcyclic 12) 12 : Subgroup (finiteCyclic 12))
      (finiteCyclicGenerator 12) := by
  simp

/-- A transition exists for the order-two group at level four even though
the fourth-power quotient does not have index four. -/
theorem two_fourth_to_second_without_exact_index :
    Function.Surjective (powerImage_quotientMap (finiteCyclic 2)
      (finiteCyclic_isProcyclic 2) (by decide : 2 ∣ 4)) ∧
      (powerImage (finiteCyclic 2) (finiteCyclic_isProcyclic 2) 4 :
        Subgroup (finiteCyclic 2)).index ≠ 4 :=
  ⟨powerImage_quotientMap_surjective _ _ (by decide : 2 ∣ 4),
    ProcyclicPowerIndexTests.two_fourth_not_exact⟩

end ProcyclicPowerTransitionTests
