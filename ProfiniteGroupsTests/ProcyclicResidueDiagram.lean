/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicResidueLimit
public import ProfiniteGroupsTests.ProcyclicPowerLimit

/-!
# Residue-diagram boundary clients

These examples use the residue stages and reduction maps directly. None uses
the natural comparison between the residue and power-quotient diagrams.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp ProcyclicPowerLimitTests

universe u

namespace ProcyclicResidueDiagramTests

/-- Every supported residue level is positive, even for empty support. -/
theorem no_zero_residue_level (S : Set Nat.Primes) (n : Nat.PowerIndex S) :
    n.val ≠ 0 := n.pos.ne'

/-- The only empty-support residue level is modulus one. -/
theorem empty_support_only_one (n : Nat.PowerIndex (∅ : Set Nat.Primes)) :
    n.val = 1 := by
  rw [Nat.PowerIndex.eq_top_of_empty n]
  exact Nat.PowerIndex.top_val

/-- The terminal coordinate is trivial for every prime support. -/
theorem terminal_residue_is_one (S : Set Nat.Primes)
    (a : (residueDiagram.{u} S).obj (⊤ : Nat.PowerIndex S)) : a = 1 := by
  exact @Subsingleton.elim (ULift.{u} (Multiplicative (ZMod 1))) inferInstance a 1

/-- At a genuine pro-2 fourth-power level, reduction of three modulo two
gives one. -/
theorem two_primary_four_to_two_residue :
    (residueDiagram.{u}
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).map
        (homOfLE (show indexFour.{u} ≤ indexTwo.{u} by
          apply (Nat.PowerIndex.le_iff _ _).mpr
          decide))
        (ULift.up (Multiplicative.ofAdd (3 : ZMod 4))) =
      ULift.up (Multiplicative.ofAdd (1 : ZMod 2)) := by
  change (residueDiagram.{u}
    {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).map
      (homOfLE (show indexFour.{u} ≤ indexTwo.{u} by
        apply (Nat.PowerIndex.le_iff _ _).mpr
        decide))
      (ULift.up (Multiplicative.ofAdd (3 : ZMod (indexFour.{u}).val))) =
    ULift.up (Multiplicative.ofAdd (1 : ZMod (indexTwo.{u}).val))
  rw [residueDiagram_map_apply]
  change ULift.up (Multiplicative.ofAdd
    (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (3 : ZMod 4))) =
      ULift.up (Multiplicative.ofAdd (1 : ZMod 2))
  decide

/-- The finite diagram also reduces three modulo four to one modulo two. -/
theorem two_primary_finite_four_to_two_residue :
    (residueFiniteFunctor.{u}
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).map
        (homOfLE (show indexFour.{u} ≤ indexTwo.{u} by
          apply (Nat.PowerIndex.le_iff _ _).mpr
          decide))
        (ULift.up (Multiplicative.ofAdd (3 : ZMod 4))) =
      ULift.up (Multiplicative.ofAdd (1 : ZMod 2)) := by
  change (residueFiniteFunctor.{u}
    {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).map
      (homOfLE (show indexFour.{u} ≤ indexTwo.{u} by
        apply (Nat.PowerIndex.le_iff _ _).mpr
        decide))
      (ULift.up (Multiplicative.ofAdd (3 : ZMod (indexFour.{u}).val))) =
    ULift.up (Multiplicative.ofAdd (1 : ZMod (indexTwo.{u}).val))
  rw [residueFiniteFunctor_map_apply]
  change ULift.up (Multiplicative.ofAdd
    (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) (3 : ZMod 4))) =
      ULift.up (Multiplicative.ofAdd (1 : ZMod 2))
  decide

/-- The fourth-residue stage has four elements; a fourth-power quotient
need not, as the order-two cyclic boundary shows. -/
theorem fourth_residue_card :
    Nat.card ((residueFiniteFunctor.{u} (Set.univ : Set Nat.Primes)).obj
      (Nat.PowerIndex.ofPositive 4 (by decide))) = 4 := by
  rw [residueFiniteFunctor_obj]
  rw [Nat.card_ulift]
  exact Nat.card_zmod 4

/-- The identity arrow fixes the nontrivial fourth-power residue. -/
theorem two_primary_residue_coherence :
    (residueDiagram.{u}
      {p | twoPrimary_isProcyclic.{u}.exponents p = ⊤}).map
        (𝟙 indexFour.{u}) (ULift.up (Multiplicative.ofAdd (3 : ZMod 4))) =
      ULift.up (Multiplicative.ofAdd (3 : ZMod 4)) := by
  exact residueDiagram_map_id_apply _ _ _

/-- The order-two cyclic group has no infinite-exponent primes, although
its fourth-power quotient has order two rather than four. -/
theorem finite_two_support_empty :
    {p : Nat.Primes | (finiteCyclic_isProcyclic 2).exponents p = ⊤} = ∅ := by
  ext p
  simp [finiteCyclic_exponents_eq_factorization]

theorem finite_two_supported_levels_only_one
    (n : Nat.PowerIndex
      {p | (finiteCyclic_isProcyclic 2).exponents p = ⊤}) : n.val = 1 := by
  let n' : Nat.PowerIndex (∅ : Set Nat.Primes) :=
    ⟨n.val, by simpa only [← finite_two_support_empty] using n.property⟩
  exact empty_support_only_one n'

theorem finite_two_fourth_order_boundary :
    Nat.card ((powerQuotientFiniteFunctor (finiteCyclic 2)
      (finiteCyclic_isProcyclic 2) (Set.univ : Set Nat.Primes)).obj
        (Nat.PowerIndex.ofPositive 4 (by decide))) = 2 :=
  finite_two_fourth_not_exact.1

end ProcyclicResidueDiagramTests
