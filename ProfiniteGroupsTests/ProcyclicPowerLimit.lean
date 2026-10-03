/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicPowerLimit
public import ProfiniteGroups.ProcyclicRealization
public import ProfiniteGroupsTests.ProcyclicPower

/-!
# Power-quotient inverse-system clients

The index, transition and canonical-map calculations use the power-quotient
diagrams. The reconstruction clients exercise the all-positive limit for
finite cyclic groups and the supported limit for torsion-free examples.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp

universe u v

namespace ProcyclicPowerLimitTests

example (S : Set Nat.Primes) : CategoryTheory.IsCofiltered (Nat.PowerIndex S) := by
  infer_instance

example : CategoryTheory.IsCofiltered (Nat.PowerIndex (∅ : Set Nat.Primes)) := by
  infer_instance

/-- Definition-only: even at full support, zero is not a level. -/
theorem no_zero_level (n : Nat.PowerIndex (Set.univ : Set Nat.Primes)) :
    n.val ≠ 0 := n.pos.ne'

/-- Definition-only: empty prime support has exactly its terminal level. -/
theorem empty_support_level (n : Nat.PowerIndex (∅ : Set Nat.Primes)) :
    n.val = 1 := by
  rw [Nat.PowerIndex.eq_top_of_empty n]
  rfl

/-- Definition-only: every procyclic group's first-power quotient collapses
the class of any element. -/
theorem one_power_coordinate (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (S : Set Nat.Primes) (g : G) :
    (powerQuotientCone G hG S).π.app (⊤ : Nat.PowerIndex S) g = 1 := by
  rw [powerQuotientCone_π_apply]
  apply (QuotientGroup.eq_one_iff g).mpr
  rw [Nat.PowerIndex.top_val, powerImage_one]
  exact Subgroup.mem_top g

/-- Definition-only: the same first-power coordinate is trivial in the
one-element profinite group, independent of the chosen prime support. -/
theorem trivial_group_coordinate (S : Set Nat.Primes) :
    (powerQuotientCone (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))
      ProfiniteGrp.punit_isProcyclic S).π.app ⊤ PUnit.unit = 1 := by
  exact one_power_coordinate _ _ S _

/-- Definition-only: the one-element cyclic group has no infinite-exponent
prime, so its supported diagram has only the first-power level. -/
theorem finite_one_support_empty :
    {p : Nat.Primes | (finiteCyclic_isProcyclic 1).exponents p = ⊤} = ∅ := by
  ext p
  simp [finiteCyclic_exponents_eq_factorization]

def twoPrimaryExponents (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then ⊤ else 0

noncomputable abbrev twoPrimary : ProfiniteGrp.{u} :=
  primewisePadicProcyclicModel.{u} twoPrimaryExponents

theorem twoPrimary_isProcyclic : IsProcyclic twoPrimary.{u} :=
  primewisePadicProcyclicModel_isProcyclic twoPrimaryExponents

local instance : IsMulCommutative twoPrimary.{u} :=
  twoPrimary_isProcyclic.{u}.isMulCommutative

theorem twoPrimary_exponents (p : Nat.Primes) :
    twoPrimary_isProcyclic.{u}.exponents p = twoPrimaryExponents p := by
  exact congrFun (primewisePadicProcyclicModel_exponents.{u}
    twoPrimaryExponents twoPrimary_isProcyclic.{u}) p

theorem twoPrimary_isMulTorsionFree : IsMulTorsionFree twoPrimary.{u} := by
  let g := primewisePadicRealizationGenerator.{u} twoPrimaryExponents
  have hg : IsTopologicalGenerator twoPrimary.{u} g :=
    primewisePadicRealizationGenerator_isTopologicalGenerator twoPrimaryExponents
  apply (isMulTorsionFree_iff_exponentsOfGenerator twoPrimary.{u} g hg).mpr
  intro p
  have heq := congrFun (twoPrimary_isProcyclic.{u}.exponents_eq_of_generator g hg) p
  rw [← heq, twoPrimary_exponents]
  by_cases hp : p.1 = 2
  · right
    simp [twoPrimaryExponents, hp]
  · left
    simp [twoPrimaryExponents, hp]

theorem two_supported :
    2 ∈ Nat.primeSupportedIndices
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤} := by
  apply (Nat.prime_mem_primeSupportedIndices_iff (⟨2, by decide⟩ : Nat.Primes)).mpr
  change twoPrimary_isProcyclic.{u}.exponents (⟨2, by decide⟩ : Nat.Primes) = ⊤
  exact (twoPrimary_exponents.{u} (⟨2, by decide⟩ : Nat.Primes)).trans
    (by simp [twoPrimaryExponents])

theorem four_supported :
    4 ∈ Nat.primeSupportedIndices
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤} := by
  convert (Nat.primeSupportedIndices
    {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).mul_mem
      two_supported.{u} two_supported.{u} using 1

def indexTwo : Nat.PowerIndex
    {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤} :=
  Nat.PowerIndex.ofSupported 2 two_supported.{u}

def indexFour : Nat.PowerIndex
    {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤} :=
  Nat.PowerIndex.ofSupported 4 four_supported.{u}

/-- Definition-only: the two-primary levels `2` and `4` have the stated
nontrivial indices, rather than merely being formal indexing labels. -/
theorem two_primary_levels_exact :
    (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 2 :
      Subgroup twoPrimary.{u}).index = 2 ∧
    (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 4 :
      Subgroup twoPrimary.{u}).index = 4 := by
  constructor
  · exact (powerImage_index_eq_iff_primeSupportedIndices _ _
      twoPrimary_isMulTorsionFree.{u} 2 (by decide)).mpr two_supported.{u}
  · exact (powerImage_index_eq_iff_primeSupportedIndices _ _
      twoPrimary_isMulTorsionFree.{u} 4 (by decide)).mpr four_supported.{u}

/-- Definition-only: the finite diagram has four elements at the supported
fourth-power level of the two-primary model. -/
theorem two_primary_finite_fourth_card :
    Nat.card ((powerQuotientFiniteFunctor twoPrimary.{u} twoPrimary_isProcyclic.{u}
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).obj indexFour.{u}) = 4 := by
  rw [powerQuotientFiniteFunctor_card]
  exact two_primary_levels_exact.{u}.2

/-- Definition-only: the identity arrow fixes a genuine fourth-power class. -/
theorem two_primary_identity (g : twoPrimary.{u}) :
    (powerQuotientDiagram twoPrimary.{u} twoPrimary_isProcyclic.{u}
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).map
      (𝟙 indexFour.{u})
      (QuotientGroup.mk' (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 4 :
        Subgroup twoPrimary.{u}) g) =
    QuotientGroup.mk' (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 4 :
      Subgroup twoPrimary.{u}) g := by
  rfl

/-- Definition-only: the four-to-two transition in the nontrivial pro-2
diagram sends a fourth-power class to its class modulo squares. -/
theorem two_primary_four_to_two (g : twoPrimary.{u}) :
    (powerQuotientDiagram twoPrimary.{u} twoPrimary_isProcyclic.{u}
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).map
      (CategoryTheory.homOfLE (show indexFour.{u} ≤ indexTwo.{u} by
        apply (Nat.PowerIndex.le_iff _ _).mpr
        decide))
      (QuotientGroup.mk' (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 4 :
        Subgroup twoPrimary.{u}) g) =
    QuotientGroup.mk' (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 2 :
      Subgroup twoPrimary.{u}) g := by
  exact powerQuotientDiagram_map_mk twoPrimary.{u} twoPrimary_isProcyclic.{u}
    {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}
    (CategoryTheory.homOfLE (show indexFour.{u} ≤ indexTwo.{u} by
      apply (Nat.PowerIndex.le_iff _ _).mpr
      decide)) g

/-- Definition-only: the four-to-two construction remains polymorphic in
the universe of the ambient pro-2 group. -/
theorem two_primary_universe_clients (g : twoPrimary.{u}) (h : twoPrimary.{v}) :
    (toPowerQuotientLimit twoPrimary.{u} twoPrimary_isProcyclic.{u}
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤} g).val indexTwo.{u} =
        QuotientGroup.mk' (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 2 :
          Subgroup twoPrimary.{u}) g ∧
    (toPowerQuotientLimit twoPrimary.{v} twoPrimary_isProcyclic.{v}
      {p | twoPrimary_isProcyclic.{v}.exponents p = ⊤} h).val indexFour.{v} =
        QuotientGroup.mk' (powerImage twoPrimary.{v} twoPrimary_isProcyclic.{v} 4 :
          Subgroup twoPrimary.{v}) h := by
  constructor
  · exact toPowerQuotientLimit_apply _ _ _ indexTwo.{u} g
  · exact toPowerQuotientLimit_apply _ _ _ indexFour.{v} h

/-- The all-positive equivalence recovers the class
of a generator in a finite cyclic group, which need not be torsion-free. -/
theorem finite_cyclic_reconstruction_client :
    ((continuousMulEquivPowerQuotientLimit (finiteCyclic 4)
      (finiteCyclic_isProcyclic 4) (finiteCyclicGenerator 4)).val
      (Nat.PowerIndex.ofPositive 2 (by decide))) =
        QuotientGroup.mk' (powerImage (finiteCyclic 4)
          (finiteCyclic_isProcyclic 4) 2 : Subgroup (finiteCyclic 4))
          (finiteCyclicGenerator 4) := by
  exact continuousMulEquivPowerQuotientLimit_apply _ _ _ _

/-- Definition-only: the fourth-power quotient of the order-two cyclic group
has two elements, not four; the all-positive diagram uses actual power
quotients rather than unconditional fourth-residue coordinates. -/
theorem finite_two_fourth_not_exact :
    Nat.card ((powerQuotientFiniteFunctor (finiteCyclic 2)
      (finiteCyclic_isProcyclic 2) (Set.univ : Set Nat.Primes)).obj
      (Nat.PowerIndex.ofPositive 4 (by decide))) = 2 ∧
    Nat.card ((powerQuotientFiniteFunctor (finiteCyclic 2)
      (finiteCyclic_isProcyclic 2) (Set.univ : Set Nat.Primes)).obj
      (Nat.PowerIndex.ofPositive 4 (by decide))) ≠ 4 := by
  rw [powerQuotientFiniteFunctor_card, Nat.PowerIndex.ofPositive_val]
  exact ⟨ProcyclicPowerTest.two_fourth_index, by
    rw [ProcyclicPowerTest.two_fourth_index]
    decide⟩

/-- The all-positive equivalence still supplies the
fourth-power class in a finite cyclic group with non-exact index. -/
theorem finite_two_fourth_reconstruction_client :
    ((continuousMulEquivPowerQuotientLimit (finiteCyclic 2)
      (finiteCyclic_isProcyclic 2) (finiteCyclicGenerator 2)).val
      (Nat.PowerIndex.ofPositive 4 (by decide))) =
        QuotientGroup.mk' (powerImage (finiteCyclic 2)
          (finiteCyclic_isProcyclic 2) 4 : Subgroup (finiteCyclic 2))
          (finiteCyclicGenerator 2) := by
  exact continuousMulEquivPowerQuotientLimit_apply _ _ _ _

/-- Definition-only: the finite cyclic all-positive example is not
torsion-free, so the supported reconstruction does not apply to it. -/
theorem finite_four_not_torsion_free : ¬ IsMulTorsionFree (finiteCyclic 4) := by
  intro hfree
  have hfree' : IsMulTorsionFree (Multiplicative (ZMod 4)) := hfree
  have hnontrivial : Multiplicative.ofAdd (1 : ZMod 4) ≠
      (1 : Multiplicative (ZMod 4)) := by decide
  have hpow : (Multiplicative.ofAdd (1 : ZMod 4)) ^ 4 =
      (1 : Multiplicative (ZMod 4)) := by
    change (4 • (1 : ZMod 4)) = 0
    decide
  exact hnontrivial (hfree'.pow_left_injective (n := 4) (by decide)
    (by simpa only [one_pow] using hpow))

/-- The support-restricted reconstruction of the trivial
cyclic group has a trivial first-power coordinate. -/
theorem finite_one_supported_reconstruction_client (g : finiteCyclic 1) :
    ((continuousMulEquivSupportedPowerQuotientLimit (finiteCyclic 1)
      (finiteCyclic_isProcyclic 1)
      (by
        have htrivial : Subsingleton (finiteCyclic 1) := by
          change Subsingleton (Multiplicative (ZMod 1))
          infer_instance
        exact @Subsingleton.to_isMulTorsionFree (finiteCyclic 1) _ htrivial) g).val
      (⊤ : Nat.PowerIndex
        {p | (finiteCyclic_isProcyclic 1).exponents p = ⊤})) = 1 := by
  rw [continuousMulEquivSupportedPowerQuotientLimit_apply]
  apply (QuotientGroup.eq_one_iff g).mpr
  rw [Nat.PowerIndex.top_val, powerImage_one]
  exact Subgroup.mem_top g

/-- The support-restricted equivalence projects a
torsion-free pro-2 group to its fourth-power quotient. -/
theorem two_primary_supported_reconstruction_client (g : twoPrimary.{u}) :
    ((continuousMulEquivSupportedPowerQuotientLimit twoPrimary.{u}
      twoPrimary_isProcyclic.{u} twoPrimary_isMulTorsionFree.{u} g).val
      indexFour.{u}) =
    QuotientGroup.mk' (powerImage twoPrimary.{u} twoPrimary_isProcyclic.{u} 4 :
      Subgroup twoPrimary.{u}) g := by
  exact continuousMulEquivSupportedPowerQuotientLimit_apply _ _ _ _ _

end ProcyclicPowerLimitTests
