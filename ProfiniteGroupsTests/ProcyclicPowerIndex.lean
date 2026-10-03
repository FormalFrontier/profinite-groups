/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicPowerIndex
public import ProfiniteGroups.ProcyclicRealization
public import ProfiniteGroupsTests.ProcyclicPower

/-!
# Exact-power-index clients

The one-power index and the finite cyclic indices used as premises are proved
independently of the primewise criterion. The single infinite two-primary model
has exponent infinity at two and zero at all other primes.
-/

@[expose] public section

open ProfiniteGrp

universe u

namespace ProcyclicPowerIndexTests

theorem one_index (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) :
    (powerImage G hG 1 : Subgroup G).index = 1 := by
  rw [powerImage_one, Subgroup.index_top]

theorem one_exponents (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) :
    ∀ p : Nat.Primes, ((1 : ℕ).factorization p.1 : ℕ∞) ≤ hG.exponents p :=
  (powerImage_index_eq_iff_exponents G hG 1 (by decide)).mp (one_index G hG)

theorem trivial_seventh_index :
    (powerImage (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))
      ProfiniteGrp.punit_isProcyclic 7 :
      Subgroup (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))).index = 1 := by
  rw [ProcyclicPowerTest.trivial_power_top, Subgroup.index_top]

theorem trivial_seventh_not_exact :
    (powerImage (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))
      ProfiniteGrp.punit_isProcyclic 7 :
      Subgroup (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))).index ≠ 7 := by
  rw [trivial_seventh_index]
  decide

theorem trivial_zero_index :
    (powerImage (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))
      ProfiniteGrp.punit_isProcyclic 0 :
      Subgroup (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))).index = 1 := by
  have htop : (powerImage (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))
      ProfiniteGrp.punit_isProcyclic 0 :
      Subgroup (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))) = ⊤ := by
    ext x
    change PUnit at x
    change (∃ y : PUnit, y ^ 0 = x) ↔ True
    exact ⟨fun _ => trivial, fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩⟩
  rw [htop, Subgroup.index_top]

theorem trivial_zero_factorization_bound :
    ∀ p : Nat.Primes, ((0 : ℕ).factorization p.1 : ℕ∞) ≤
      ProfiniteGrp.punit_isProcyclic.exponents p := by
  intro p
  simp [Nat.factorization_zero]

theorem trivial_zero_not_exact :
    (powerImage (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))
      ProfiniteGrp.punit_isProcyclic 0 :
      Subgroup (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))).index ≠ 0 := by
  rw [trivial_zero_index]
  decide

theorem four_square_exponents :
    ∀ p : Nat.Primes, ((2 : ℕ).factorization p.1 : ℕ∞) ≤
      (finiteCyclic_isProcyclic 4).exponents p :=
  (powerImage_index_eq_iff_exponents _ _ 2 (by decide)).mp
    ProcyclicPowerTest.four_square_index

theorem four_square_quotient_generator_forward :
    powerImage_zmodContinuousMulEquiv (finiteCyclic 4)
      (finiteCyclic_isProcyclic 4) (finiteCyclicGenerator 4)
      (finiteCyclicGenerator_isTopologicalGenerator 4) 2 (by decide)
      ProcyclicPowerTest.four_square_index (Multiplicative.ofAdd (1 : ZMod 2)) =
        (QuotientGroup.mk' (powerImage (finiteCyclic 4)
          (finiteCyclic_isProcyclic 4) 2 : Subgroup (finiteCyclic 4)))
            (finiteCyclicGenerator 4) := by
  exact powerImage_zmodContinuousMulEquiv_apply_one (finiteCyclic 4)
    (finiteCyclic_isProcyclic 4) (finiteCyclicGenerator 4)
    (finiteCyclicGenerator_isTopologicalGenerator 4) 2 (by decide)
    ProcyclicPowerTest.four_square_index

theorem four_square_quotient_generator :
    (powerImage_zmodContinuousMulEquiv (finiteCyclic 4)
      (finiteCyclic_isProcyclic 4) (finiteCyclicGenerator 4)
      (finiteCyclicGenerator_isTopologicalGenerator 4) 2 (by decide)
      ProcyclicPowerTest.four_square_index).symm
        ((QuotientGroup.mk' (powerImage (finiteCyclic 4)
          (finiteCyclic_isProcyclic 4) 2 : Subgroup (finiteCyclic 4)))
            (finiteCyclicGenerator 4)) = Multiplicative.ofAdd (1 : ZMod 2) := by
  exact powerImage_zmodContinuousMulEquiv_symm_apply_generator (finiteCyclic 4)
    (finiteCyclic_isProcyclic 4) (finiteCyclicGenerator 4)
    (finiteCyclicGenerator_isTopologicalGenerator 4) 2 (by decide)
    ProcyclicPowerTest.four_square_index

theorem four_square_quotient_generator_ne_one :
    (powerImage_zmodContinuousMulEquiv (finiteCyclic 4)
      (finiteCyclic_isProcyclic 4) (finiteCyclicGenerator 4)
      (finiteCyclicGenerator_isTopologicalGenerator 4) 2 (by decide)
      ProcyclicPowerTest.four_square_index).symm
        ((QuotientGroup.mk' (powerImage (finiteCyclic 4)
          (finiteCyclic_isProcyclic 4) 2 : Subgroup (finiteCyclic 4)))
            (finiteCyclicGenerator 4)) ≠ 1 := by
  simp only [powerImage_zmodContinuousMulEquiv_symm_apply_generator]
  decide

theorem two_fourth_not_exact :
    (powerImage (finiteCyclic 2) (finiteCyclic_isProcyclic 2) 4 :
      Subgroup (finiteCyclic 2)).index ≠ 4 := by
  rw [ProcyclicPowerTest.two_fourth_index]
  decide

theorem two_fourth_exponents_fail :
    ¬ ∀ p : Nat.Primes, ((4 : ℕ).factorization p.1 : ℕ∞) ≤
      (finiteCyclic_isProcyclic 2).exponents p := by
  intro h
  exact two_fourth_not_exact
    ((powerImage_index_eq_iff_exponents _ _ 4 (by decide)).mpr h)

private def twoPrimaryExponents (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then ⊤ else 0

private noncomputable abbrev twoPrimary : ProfiniteGrp.{u} :=
  primewisePadicProcyclicModel.{u} twoPrimaryExponents

private theorem twoPrimary_isProcyclic : IsProcyclic twoPrimary.{u} :=
  primewisePadicProcyclicModel_isProcyclic twoPrimaryExponents

private theorem twoPrimary_exponents (p : Nat.Primes) :
    twoPrimary_isProcyclic.{u}.exponents p = twoPrimaryExponents p := by
  exact congrFun (primewisePadicProcyclicModel_exponents.{u}
    twoPrimaryExponents twoPrimary_isProcyclic.{u}) p

private theorem twoPrimary_isMulTorsionFree : IsMulTorsionFree twoPrimary.{u} := by
  let g := primewisePadicRealizationGenerator.{u} twoPrimaryExponents
  have hg : IsTopologicalGenerator twoPrimary.{u} g :=
    primewisePadicRealizationGenerator_isTopologicalGenerator twoPrimaryExponents
  apply (isMulTorsionFree_iff_exponentsOfGenerator twoPrimary.{u} g hg).mpr
  intro p
  have heq := congrFun (twoPrimary_isProcyclic.{u}.exponents_eq_of_generator g hg) p
  rw [← heq, twoPrimary_exponents]
  by_cases htwo : p.1 = 2
  · right
    simp [twoPrimaryExponents, htwo]
  · left
    simp [twoPrimaryExponents, htwo]

private theorem twoPrimary_fourth_index :
    (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 4 :
      Subgroup twoPrimary.{u}).index = 4 := by
  apply (powerImage_index_eq_iff_exponents _ _ 4 (by decide)).mpr
  intro p
  rw [twoPrimary_exponents]
  by_cases htwo : p.1 = 2
  · simp [twoPrimaryExponents, htwo]
  · have hzero : (4 : ℕ).factorization p.1 = 0 := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide,
        (by decide : Nat.Prime 2).factorization_pow]
      simp [htwo]
    simp [twoPrimaryExponents, htwo, hzero]

private theorem twoPrimary_fourth_torsionFree_support :
    ∀ p : Nat.Primes, (4 : ℕ).factorization p.1 ≠ 0 →
      twoPrimary_isProcyclic.{u}.exponents p = ⊤ :=
  (powerImage_index_eq_iff_exponents_top_of_isMulTorsionFree
    twoPrimary.{u} twoPrimary_isProcyclic.{u} twoPrimary_isMulTorsionFree.{u}
    4 (by decide)).mp twoPrimary_fourth_index

private theorem twoPrimary_third_index_one :
    (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 3 :
      Subgroup twoPrimary.{u}).index = 1 := by
  have hbad : ¬ ∀ p : Nat.Primes, ((3 : ℕ).factorization p.1 : ℕ∞) ≤
      twoPrimary_isProcyclic.{u}.exponents p := by
    intro h
    let p3 : Nat.Primes := ⟨3, by decide⟩
    have hp := h p3
    rw [twoPrimary_exponents p3] at hp
    have hfactor : (3 : ℕ).factorization p3.1 = 1 := by
      exact Nat.Prime.factorization_self (by decide : Nat.Prime 3)
    rw [hfactor] at hp
    norm_num [twoPrimaryExponents, p3] at hp
  have hnot := (powerImage_index_eq_iff_exponents _ _ 3 (by decide)).not.mpr hbad
  have hdiv := powerImage_index_dvd twoPrimary.{u} twoPrimary_isProcyclic.{u}
    3 (by decide)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdiv with hone | hthree
  · exact hone
  · exact (hnot hthree).elim

end ProcyclicPowerIndexTests

end
