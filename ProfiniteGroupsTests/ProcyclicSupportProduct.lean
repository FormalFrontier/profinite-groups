/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicSupportProduct
public import ProfiniteGroups.ProcyclicRealization

/-!
# Boundary clients for the procyclic support product

Empty, finite-only, infinite-only and mixed supports exercise the coordinate
maps. The finite and infinite examples use different prime coordinates.
The everywhere-one family has infinite positive finite support. The inverse
map restores zero-exponent coordinates as zero.
-/

@[expose] public section

open ProfiniteGrp

namespace ProcyclicSupportProductTests

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private def twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
private def threePrime : Nat.Primes := ⟨3, by decide⟩
private def fivePrime : Nat.Primes := ⟨5, by decide⟩

private def zeroExponent (_ : Nat.Primes) : ℕ∞ := 0

private def finiteExponent (p : Nat.Primes) : ℕ∞ :=
  if p = twoPrime then 2 else 0

private def everywhereOneExponent (_ : Nat.Primes) : ℕ∞ := 1

private theorem everywhereOneExponent_support (p : Nat.Primes) :
    0 < everywhereOneExponent p ∧ everywhereOneExponent p < ⊤ := by
  simp [everywhereOneExponent]

private def infiniteExponent (p : Nat.Primes) : ℕ∞ :=
  if p = threePrime then ⊤ else 0

private def mixedExponent (p : Nat.Primes) : ℕ∞ :=
  if p = twoPrime then 2 else if p = threePrime then ⊤ else 0

private theorem finiteExponent_two_support :
    0 < finiteExponent twoPrime ∧ finiteExponent twoPrime < ⊤ := by
  constructor
  · simp [finiteExponent]
  · simpa [finiteExponent] using (ENat.natCast_lt_top 2)

private theorem mixedExponent_two_support :
    0 < mixedExponent twoPrime ∧ mixedExponent twoPrime < ⊤ := by
  constructor
  · simp [mixedExponent]
  · simpa [mixedExponent] using (ENat.natCast_lt_top 2)

/-- A finite-only family has no infinite support. -/
example : IsEmpty {p : Nat.Primes // finiteExponent p = ⊤} := by
  refine ⟨fun p ↦ ?_⟩
  by_cases hp : p.1 = twoPrime
  · have h := p.2
    simp [finiteExponent, hp] at h
  · have h := p.2
    simp [finiteExponent, hp] at h

/-- An infinite-only family has no positive finite support. -/
example : IsEmpty {p : Nat.Primes // 0 < infiniteExponent p ∧ infiniteExponent p < ⊤} := by
  refine ⟨fun p ↦ ?_⟩
  by_cases hp : p.1 = threePrime
  · have h := p.2
    simp [infiniteExponent, hp] at h
  · have h := p.2
    simp [infiniteExponent, hp] at h

/-- The zero family has no positive finite or infinite support. -/
example : IsEmpty {p : Nat.Primes // 0 < zeroExponent p ∧ zeroExponent p < ⊤} := by
  refine ⟨fun p ↦ ?_⟩
  have hp := p.2.1
  simp [zeroExponent] at hp

example : IsEmpty {p : Nat.Primes // zeroExponent p = ⊤} := by
  refine ⟨fun p ↦ ?_⟩
  have hp := p.2
  simp [zeroExponent] at hp

/-- With both supports empty, the support product is a singleton. -/
example : Subsingleton (primewisePadicSupportProduct.{1} (fun _ ↦ 0)) := by
  refine ⟨fun x y ↦ Prod.ext ?_ ?_⟩
  · funext p
    exact ((lt_irrefl (0 : ℕ∞)) p.2.1).elim
  · funext p
    exact ((by decide : (0 : ℕ∞) ≠ ⊤) p.2).elim

/-- The all-zero quotient model also has a single element. -/
example : Subsingleton (primewisePadicQuotientModel.{1} (fun _ ↦ 0)) := by
  let equiv := primewisePadicQuotientModelContinuousAddEquivSupportProduct.{1}
    (fun _ ↦ 0)
  have htarget : Subsingleton (primewisePadicSupportProduct.{1} (fun _ ↦ 0)) := by
    refine ⟨fun x y ↦ Prod.ext ?_ ?_⟩
    · funext p
      exact ((lt_irrefl (0 : ℕ∞)) p.2.1).elim
    · funext p
      exact ((by decide : (0 : ℕ∞) ≠ ⊤) p.2).elim
  exact ⟨fun x y ↦ equiv.injective (Subsingleton.elim (equiv x) (equiv y))⟩

/-- A nonzero finite exponent keeps reduction modulo the prime square. -/
example (x : primewisePadicRing.{1}) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct finiteExponent
      (primewisePadicQuotientContinuousAddEquivModel finiteExponent
        (Ideal.Quotient.mk (primewisePadicIdealOfExponents finiteExponent) x))).1
      ⟨twoPrime, finiteExponent_two_support⟩ =
        ULift.up (PadicInt.toZModPow 2 (x twoPrime).down) := by
  rw [primewisePadicQuotientModelContinuousAddEquivSupportProduct_finite_apply,
    primewisePadicQuotientContinuousAddEquivModel_mk_apply,
    padicQuotientFactorContinuousAddEquivFinite_mk]
  rfl

/-- The positive finite support can be infinite: every prime contributes a
reduction modulo that prime, with no finite-support assumption. -/
example : Infinite {p : Nat.Primes //
    0 < everywhereOneExponent p ∧ everywhereOneExponent p < ⊤} :=
  Infinite.of_injective (fun p : Nat.Primes ↦
    (⟨p, everywhereOneExponent_support p⟩ :
      {p : Nat.Primes // 0 < everywhereOneExponent p ∧ everywhereOneExponent p < ⊤}))
    (fun _ _ h ↦ congrArg Subtype.val h)

example (x : primewisePadicRing.{1}) (p : Nat.Primes) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct everywhereOneExponent
      (primewisePadicQuotientContinuousAddEquivModel everywhereOneExponent
        (Ideal.Quotient.mk (primewisePadicIdealOfExponents everywhereOneExponent) x))).1
      ⟨p, everywhereOneExponent_support p⟩ =
        ULift.up (PadicInt.toZModPow 1 (x p).down) := by
  rw [primewisePadicQuotientModelContinuousAddEquivSupportProduct_finite_apply,
    primewisePadicQuotientContinuousAddEquivModel_mk_apply,
    padicQuotientFactorContinuousAddEquivFinite_mk]
  rfl

/-- A single infinite exponent keeps the p-adic integer coordinate. -/
example (x : primewisePadicRing.{1}) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct infiniteExponent
      (primewisePadicQuotientContinuousAddEquivModel infiniteExponent
        (Ideal.Quotient.mk (primewisePadicIdealOfExponents infiniteExponent) x))).2
      ⟨threePrime, by simp [infiniteExponent]⟩ = x threePrime := by
  rw [primewisePadicQuotientModelContinuousAddEquivSupportProduct_top_apply,
    primewisePadicQuotientContinuousAddEquivModel_mk_apply,
    padicQuotientFactorContinuousAddEquivTop_mk]

/-- The mixed model has a finite factor at two and an infinite factor at three. -/
example (x : primewisePadicSupportProduct.{1} mixedExponent) :
    ULift.{1} (ZMod (2 ^ 2)) × ULift.{1} ℤ_[3] :=
  (x.1 ⟨twoPrime, mixedExponent_two_support⟩,
    x.2 ⟨threePrime, by simp [mixedExponent, show threePrime ≠ twoPrime by decide]⟩)

/-- Both kinds of retained coordinate in one mixed quotient reduce to their
expected factors at distinct primes. -/
example (x : primewisePadicRing.{1}) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct mixedExponent
      (primewisePadicQuotientContinuousAddEquivModel mixedExponent
        (Ideal.Quotient.mk (primewisePadicIdealOfExponents mixedExponent) x))).1
        ⟨twoPrime, mixedExponent_two_support⟩ =
          ULift.up (PadicInt.toZModPow 2 (x twoPrime).down) ∧
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct mixedExponent
      (primewisePadicQuotientContinuousAddEquivModel mixedExponent
        (Ideal.Quotient.mk (primewisePadicIdealOfExponents mixedExponent) x))).2
        ⟨threePrime, by simp [mixedExponent,
          show threePrime ≠ twoPrime by decide]⟩ = x threePrime := by
  constructor
  · rw [primewisePadicQuotientModelContinuousAddEquivSupportProduct_finite_apply,
      primewisePadicQuotientContinuousAddEquivModel_mk_apply,
      padicQuotientFactorContinuousAddEquivFinite_mk]
    rfl
  · rw [primewisePadicQuotientModelContinuousAddEquivSupportProduct_top_apply,
      primewisePadicQuotientContinuousAddEquivModel_mk_apply,
      padicQuotientFactorContinuousAddEquivTop_mk]

/-- The inverse of the mixed model inserts zero away from both supports. -/
example (x : primewisePadicSupportProduct.{1} mixedExponent) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct mixedExponent).symm
        x fivePrime = 0 := by
  apply primewisePadicQuotientModelContinuousAddEquivSupportProduct_symm_apply_zero
  simp [mixedExponent, show fivePrime ≠ twoPrime by decide,
    show fivePrime ≠ threePrime by decide]

/-- The torsion-free specialization has the same retained coordinates as
the existing p-adic support-product equivalence. -/
example (x : primewisePadicQuotientModel.{1} infiniteExponent) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct infiniteExponent x).2 =
      primewisePadicQuotientModelContinuousAddEquivTopSupport infiniteExponent
        (by
          intro p
          by_cases hp : p = threePrime
          · right; simp [infiniteExponent, hp]
          · left; simp [infiniteExponent, hp]) x := by
  exact primewisePadicQuotientModelContinuousAddEquivSupportProduct_topSupport _ _ _

/-- A mixed, hence not torsion-free, procyclic group still receives the
continuous multiplicative support-product equivalence. -/
example (g : primewisePadicProcyclicModel.{1} mixedExponent) :
    (((primewisePadicProcyclicModel_isProcyclic.{1} mixedExponent).continuousMulEquivSupportProduct
      g).toAdd).1
      ⟨twoPrime, by
        rw [primewisePadicProcyclicModel_exponents]
        exact mixedExponent_two_support⟩ =
    padicQuotientFactorContinuousAddEquivFinite twoPrime
      ((primewisePadicProcyclicModel_isProcyclic.{1} mixedExponent).exponents twoPrime)
      (by
        rw [primewisePadicProcyclicModel_exponents]
        exact mixedExponent_two_support.2)
      (((primewisePadicProcyclicModel_isProcyclic.{1} mixedExponent).continuousMulEquivModel
        g).toAdd twoPrime) := by
  exact (primewisePadicProcyclicModel_isProcyclic.{1}
    mixedExponent).continuousMulEquivSupportProduct_finite_apply g _

end ProcyclicSupportProductTests
