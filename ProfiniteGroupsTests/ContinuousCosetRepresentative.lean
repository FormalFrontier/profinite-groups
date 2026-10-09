/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ContinuousCosetRepresentative
public import ProfiniteGroupsTests.ClosedQuotient

/-!
# Continuous coset representative clients

The point stabilizer in the symmetric group on three points is closed but
nonnormal. Its chosen continuous representatives separate two distinct cosets.
The bottom subgroup gives back each element, while at the top subgroup the
right-inverse equation alone cannot force normalization at the identity.
-/

@[expose] public section

set_option warningAsError true

namespace ProfiniteGroupsTests.ContinuousCosetRepresentative

open ClosedQuotientTests

instance : IsClosed (pointStabilizer.toSubgroup : Set symmetricThree) :=
  pointStabilizer.isClosed'

private instance : IsClosed ((⊥ : Subgroup symmetricThree) : Set symmetricThree) :=
  ⟨by simp⟩

/-- Distinct cosets of a finite nonnormal subgroup have distinct continuously
chosen representatives. -/
theorem nonnormal_representatives_distinct : ¬ pointStabilizer.toSubgroup.Normal ∧
    pointStabilizer.toSubgroup.continuousCosetRepresentative
      (QuotientGroup.mk (1 : symmetricThree)) ≠
    pointStabilizer.toSubgroup.continuousCosetRepresentative
      (QuotientGroup.mk (Equiv.swap (0 : Fin 3) 1 : symmetricThree)) := by
  refine ⟨pointStabilizer_not_normal, ?_⟩
  apply pointStabilizer.toSubgroup.continuousCosetRepresentative_injective.ne
  intro heq
  have hrelation := QuotientGroup.eq.mp heq
  change ((1 : Equiv.Perm (Fin 3))⁻¹ * Equiv.swap (0 : Fin 3) 1) (0 : Fin 3) = 0
    at hrelation
  exact (by decide : ((1 : Equiv.Perm (Fin 3))⁻¹ * Equiv.swap (0 : Fin 3) 1)
    (0 : Fin 3) ≠ 0) hrelation

/-- The bottom-subgroup representative of a coset of `g` is exactly `g`. -/
theorem bot_continuousCosetRepresentative_mk (g : symmetricThree) :
    ((⊥ : Subgroup symmetricThree).continuousCosetRepresentative
      (QuotientGroup.mk g : symmetricThree ⧸ (⊥ : Subgroup symmetricThree))) = g := by
  have h := (⊥ : Subgroup symmetricThree).continuousCosetRepresentative_mk
    (QuotientGroup.mk g : symmetricThree ⧸ (⊥ : Subgroup symmetricThree))
  exact eq_of_inv_mul_eq_one (Subgroup.mem_bot.mp (QuotientGroup.eq.mp h))

/-- A right inverse to the projection onto the top coset space need not send
the identity coset to the identity. -/
theorem exists_top_rightInverse_ne_one :
    ∃ s : C(symmetricThree ⧸ (⊤ : Subgroup symmetricThree), symmetricThree),
    (∀ q, QuotientGroup.mk (s q) = q) ∧
    s (QuotientGroup.mk (1 : symmetricThree)) ≠ 1 := by
  let swap : symmetricThree := Equiv.swap (0 : Fin 3) 1
  refine ⟨⟨fun _ ↦ swap, continuous_const⟩, ?_, ?_⟩
  · intro q
    exact QuotientGroup.subsingleton_quotient_top.elim _ _
  · change (Equiv.swap (0 : Fin 3) 1 : Equiv.Perm (Fin 3)) ≠ 1
    intro h
    have hfix := congrArg (fun f : Equiv.Perm (Fin 3) ↦ f 0) h
    simp at hfix

end ProfiniteGroupsTests.ContinuousCosetRepresentative
