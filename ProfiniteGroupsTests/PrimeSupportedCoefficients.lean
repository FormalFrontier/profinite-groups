/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.PrimeSupportedCoefficients

/-!
# Boundary clients for prime-supported coefficients

The concrete supported-index checks and one-smul facts do not depend on the
primewise divisibility or torsion equivalences. The ZMod examples using the
prime-order criteria depend on those criteria.
-/

@[expose] public section

namespace PrimeSupportedCoefficientsTests

/-- The prime two in the cyclic boundary examples. -/
def twoPrime : Nat.Primes := ⟨2, by decide⟩

example : (2 : ℕ) ∈ Nat.primeSupportedIndices ({twoPrime} : Set Nat.Primes) :=
  (Nat.prime_mem_primeSupportedIndices_iff twoPrime).mpr (Set.mem_singleton twoPrime)

example : (0 : ℕ) ∉ Nat.primeSupportedIndices (Set.univ : Set Nat.Primes) :=
  Nat.not_mem_primeSupportedIndices_zero _

example (a : ZMod 2) : (1 : ℕ) • a = a := by simp

example : AddMonoid.IsPrimeSupportedDivisible (ZMod 2) (∅ : Set Nat.Primes) :=
  AddMonoid.isPrimeSupportedDivisible_empty _

example (S : Set Nat.Primes) (n : Nat.primeSupportedIndices S) :
    (nsmulAddMonoidHom (α := ℚ) n.1).range = ⊤ :=
  (AddCommGroup.isPrimeSupportedDivisible_iff_nsmul_range_eq_top ℚ S).mp
    (AddMonoid.isPrimeSupportedDivisible_rat S) n

/-- The characteristic annihilates every element of `ZMod 2` without using
the primewise torsion criterion. -/
theorem two_supported_torsion : Module.IsTorsion' (ZMod 2)
    (Nat.primeSupportedIndices ({twoPrime} : Set Nat.Primes)) := by
  intro a
  refine ⟨⟨2, (Nat.prime_mem_primeSupportedIndices_iff twoPrime).mpr
    (Set.mem_singleton _)⟩, ?_⟩
  exact ZModModule.char_nsmul_eq_zero 2 a

example :
    (⨆ n : Nat.primeSupportedIndices ({twoPrime} : Set Nat.Primes),
      Submodule.torsionBy ℤ (ZMod 2) (n.1 : ℤ)) = ⊤ := by
  rw [← Submodule.torsion'_primeSupportedIndices_eq_iSup_torsionBy]
  exact (Submodule.isTorsion'_iff_torsion'_eq_top
    (R := ℤ) (M := ZMod 2) (Nat.primeSupportedIndices ({twoPrime} : Set Nat.Primes))).mp
      two_supported_torsion

example : Module.IsTorsion' (ZMod 2)
    (Nat.primeSupportedIndices ({twoPrime} : Set Nat.Primes)) :=
  (Module.isTorsion'_zmod_prime_iff twoPrime {twoPrime}).mpr (Set.mem_singleton _)

example : ¬ Module.IsTorsion' (ZMod 2)
    (Nat.primeSupportedIndices (∅ : Set Nat.Primes)) := by
  intro h
  have hp := (Module.isTorsion'_zmod_prime_iff twoPrime ∅).mp h
  exact hp.elim

example : ¬ AddMonoid.IsPrimeSupportedDivisible (ZMod 2)
    ({twoPrime} : Set Nat.Primes) := by
  intro h
  have hp := (AddMonoid.isPrimeSupportedDivisible_zmod_prime_iff
    twoPrime {twoPrime}).mp h
  exact hp (Set.mem_singleton twoPrime)

example : AddMonoid.IsPrimeSupportedDivisible (ZMod 2)
    (∅ : Set Nat.Primes) := by
  exact (AddMonoid.isPrimeSupportedDivisible_zmod_prime_iff twoPrime ∅).mpr
    (by simp)

end PrimeSupportedCoefficientsTests
