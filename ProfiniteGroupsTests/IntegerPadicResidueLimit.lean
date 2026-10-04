/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.IntegerPadicResidueLimit

/-!
# P-power and all-positive residue-limit clients

These clients distinguish the modulus-one boundaries from nontrivial
reductions, and evaluate the two canonical comparisons on integral units.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp

universe u

namespace IntegerPadicResidueLimitTests

/-- The prime used in the p-power boundary tests. -/
def two : Nat.Primes := ⟨2, by decide⟩

local instance : Fact two.1.Prime := ⟨two.2⟩

/-- The modulus-two all-positive residue index. -/
def indexTwo : Nat.PowerIndex (Set.univ : Set Nat.Primes) :=
  Nat.PowerIndex.ofPositive 2 (by decide)

/-- The modulus-three all-positive residue index. -/
def indexThree : Nat.PowerIndex (Set.univ : Set Nat.Primes) :=
  Nat.PowerIndex.ofPositive 3 (by decide)

/-- The modulus-four all-positive residue index. -/
def indexFour : Nat.PowerIndex (Set.univ : Set Nat.Primes) :=
  Nat.PowerIndex.ofPositive 4 (by decide)

/-- The modulus-six all-positive residue index. -/
def indexSix : Nat.PowerIndex (Set.univ : Set Nat.Primes) :=
  Nat.PowerIndex.ofPositive 6 (by decide)

/-- At exponent zero the p-power residue group has just one element. -/
theorem zero_p_power_coordinate_subsingleton
    (a : (pPowerResidueDiagram.{u} two).obj (OrderDual.toDual 0)) : a = 1 := by
  exact @Subsingleton.elim (ULift.{u} (Multiplicative (ZMod 1))) inferInstance a 1

/-- The integral p-adic unit is distinct from multiplicative identity,
which represents additive zero. -/
theorem p_adic_integral_unit_ne_identity :
    padicFactorGenerator.{u} two ≠ 1 := by
  intro h
  have hzero := congrArg
    (fun a : padicFactor.{u} two ↦ a.toAdd.down) h
  change (1 : ℤ_[2]) = 0 at hzero
  exact one_ne_zero hzero

/-- The all-positive index also contains its trivial modulus-one level. -/
theorem unit_modulus_coordinate_subsingleton
    (a : (residueDiagram.{u} (Set.univ : Set Nat.Primes)).obj
      (⊤ : Nat.PowerIndex (Set.univ : Set Nat.Primes))) : a = 1 := by
  exact @Subsingleton.elim (ULift.{u} (Multiplicative (ZMod 1))) inferInstance a 1

/-- The p-power diagram genuinely reduces three modulo four to one modulo two. -/
theorem p_power_four_to_two :
    (pPowerResidueDiagram.{u} two).map
        (homOfLE (show OrderDual.toDual 2 ≤ OrderDual.toDual 1 from (by decide)))
      (ULift.up (Multiplicative.ofAdd (3 : ZMod 4))) =
      ULift.up (Multiplicative.ofAdd (1 : ZMod 2)) := by
  have hmap := pPowerResidueDiagram_map_apply.{u} two
    (homOfLE (show OrderDual.toDual 2 ≤ OrderDual.toDual 1 from (by decide)))
    (3 : ZMod (two.1 ^ 2))
  exact hmap.trans (congrArg
    (fun a : ZMod 2 ↦ ULift.up (Multiplicative.ofAdd a))
    (by
      calc
        _ = (3 : ZMod 2) := map_natCast
          (ZMod.castHom (pow_dvd_pow two.1 (show 1 ≤ 2 by decide)) (ZMod 2)) 3
        _ = 1 := by decide))

/-- Modulo six, five reduces to one modulo two. -/
theorem six_to_two :
    (residueDiagram.{u} (Set.univ : Set Nat.Primes)).map
        (homOfLE (show indexSix ≤ indexTwo by
          apply (Nat.PowerIndex.le_iff _ _).mpr
          decide))
        (ULift.up (Multiplicative.ofAdd (5 : ZMod 6))) =
      ULift.up (Multiplicative.ofAdd (1 : ZMod 2)) := by
  change (residueDiagram.{u} (Set.univ : Set Nat.Primes)).map
      (homOfLE (show indexSix ≤ indexTwo by
        apply (Nat.PowerIndex.le_iff _ _).mpr
        decide))
      (ULift.up (Multiplicative.ofAdd (5 : ZMod indexSix.val))) =
    ULift.up (Multiplicative.ofAdd (1 : ZMod indexTwo.val))
  rw [residueDiagram_map_apply]
  change ULift.up (Multiplicative.ofAdd
      (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2) (5 : ZMod 6))) = _
  exact congrArg (fun a : ZMod 2 ↦ ULift.up (Multiplicative.ofAdd a))
    (by
      calc
        _ = (5 : ZMod 2) := map_natCast
          (ZMod.castHom (by decide : 2 ∣ 6) (ZMod 2)) 5
        _ = 1 := by decide)

/-- The other reduction from six distinguishes the residue of five from one. -/
theorem six_to_three :
    (residueDiagram.{u} (Set.univ : Set Nat.Primes)).map
        (homOfLE (show indexSix ≤ indexThree by
          apply (Nat.PowerIndex.le_iff _ _).mpr
          decide))
        (ULift.up (Multiplicative.ofAdd (5 : ZMod 6))) =
      ULift.up (Multiplicative.ofAdd (2 : ZMod 3)) := by
  change (residueDiagram.{u} (Set.univ : Set Nat.Primes)).map
      (homOfLE (show indexSix ≤ indexThree by
        apply (Nat.PowerIndex.le_iff _ _).mpr
        decide))
      (ULift.up (Multiplicative.ofAdd (5 : ZMod indexSix.val))) =
    ULift.up (Multiplicative.ofAdd (2 : ZMod indexThree.val))
  rw [residueDiagram_map_apply]
  change ULift.up (Multiplicative.ofAdd
      (ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3) (5 : ZMod 6))) = _
  exact congrArg (fun a : ZMod 3 ↦ ULift.up (Multiplicative.ofAdd a))
    (by
      calc
        _ = (5 : ZMod 3) := map_natCast
          (ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3)) 5
        _ = 2 := by decide)

/-- Reduction from modulus six to modulus two agrees with the
completed-integer residues at these moduli. -/
theorem completion_residue_six_to_two (x : integerCompletion.{u}) :
    (residueDiagram.{u} (Set.univ : Set Nat.Primes)).map
        (homOfLE (show indexSix ≤ indexTwo by
          apply (Nat.PowerIndex.le_iff _ _).mpr
          decide))
        (ULift.up (Multiplicative.ofAdd (integerCompletionResidueAt indexSix x))) =
      ULift.up (Multiplicative.ofAdd (integerCompletionResidueAt indexTwo x)) :=
  integerCompletionResidueAt_map _ x

/-- An element whose every finite residue is one is the integral generator;
this uniqueness uses only the completion residue maps. -/
theorem completion_eq_generator_of_residues (x : integerCompletion.{u})
    (h : ∀ n : Nat.PowerIndex (Set.univ : Set Nat.Primes),
      integerCompletionResidueAt n x = 1) :
    x = integerCompletionGenerator := by
  apply integerCompletionResidueAt_ext
  intro n
  simpa only [integerCompletionGenerator, integerCompletionResidueAt_eta_int,
    Int.cast_one] using h n

/-- These two positive reductions are independent: the target residues differ. -/
theorem six_residues_distinguish (a : ZMod 6)
    (hb : ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3) a = 2) :
    a ≠ (1 : ZMod 6) := by
  intro heq
  rw [heq] at hb
  have hne : (1 : ZMod 3) ≠ 2 := by decide
  exact hne (by simpa only [map_one] using hb)

/-- An actual integral p-adic element has its expected nonzero fourth residue. -/
theorem p_adic_three_mod_four :
    (padicFactorEquivPowerResidueLimit.{u} two
      (Multiplicative.ofAdd (ULift.up (3 : ℤ_[2])))).val
        (OrderDual.toDual 2) =
      ULift.up (Multiplicative.ofAdd (3 : ZMod 4)) := by
  calc
    _ = ULift.up (Multiplicative.ofAdd
          (PadicInt.toZModPow 2 (3 : ℤ_[2]))) :=
        padicFactorEquivPowerResidueLimit_apply.{u} two (OrderDual.toDual 2) _
    _ = _ := congrArg (fun a : ZMod 4 ↦ ULift.up (Multiplicative.ofAdd a))
      (map_natCast (PadicInt.toZModPow 2 : ℤ_[2] →+* ZMod 4) 3)

/-- The p-adic integral unit maps to residue one, not literal group identity. -/
theorem p_adic_generator_four_coordinate :
    (padicFactorEquivPowerResidueLimit.{u} two
      (padicFactorGenerator two)).val (OrderDual.toDual 2) =
      ULift.up (Multiplicative.ofAdd (1 : ZMod 4)) :=
  padicFactorEquivPowerResidueLimit_generator two (OrderDual.toDual 2)

/-- Five in the completed integers has residue five modulo six. -/
theorem completion_five_mod_six :
    (integerCompletionEquivResidueLimit.{u}
      (ProfiniteCompletion.etaFn (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
        (ULift.up (Multiplicative.ofAdd (5 : ℤ))))).val indexSix =
      ULift.up (Multiplicative.ofAdd (5 : ZMod 6)) :=
  integerCompletionEquivResidueLimit_eta_int indexSix 5

/-- The completed-integer generator has nonzero fourth residue. -/
theorem completion_generator_four_coordinate :
    (integerCompletionEquivResidueLimit.{u} integerCompletionGenerator).val
        indexFour = ULift.up (Multiplicative.ofAdd (1 : ZMod 4)) :=
  integerCompletionEquivResidueLimit_generator indexFour

/-- The all-positive diagram excludes zero by the positive-index type. -/
theorem no_zero_all_positive_index
    (n : Nat.PowerIndex (Set.univ : Set Nat.Primes)) : n.val ≠ 0 :=
  n.pos.ne'

end IntegerPadicResidueLimitTests
