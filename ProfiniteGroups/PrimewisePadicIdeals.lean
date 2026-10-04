/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ClosedIdealPi
public import ProfiniteGroups.PrimewisePadicKernel
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Module.Compact

/-!
# Closed ideals in the primewise p-adic ring

This file classifies ideals in an uplifted p-adic factor by an exponent in
`ℕ∞`, and then classifies closed ideals in `ProfiniteGrp.primewisePadicRing`
coordinatewise.  The order on factor ideals corresponds to the reverse order
`ℕ∞ᵒᵈ`: a zero exponent gives the top ideal, while an infinite exponent gives
the zero ideal.

Exponent zero corresponds to a trivial residue quotient, while a *positive*
finite exponent corresponds to a nontrivial finite quotient. An arbitrary
infinite product ideal requires closedness to be reconstructed from factors.

## References

- Mathlib, `Mathlib.RingTheory.DiscreteValuationRing.Basic` (p-adic factor ideals);
  `ClosedIdealPi` provides the closed-product reconstruction. The factor classification is
  not asserted as a printed result in Neukirch–Schmidt–Wingberg.
-/

@[expose] public section

open Set

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Ideals in an uplifted p-adic factor, ordered by inclusion, correspond to
extended natural exponents in the reverse order.

Uses Mathlib’s p-adic ideal order and `ULift` transport; this factor classification is not
attributed to a printed procyclic theorem. -/
noncomputable def liftedPadicIdealOrderIso (p : Nat.Primes) :
    Ideal (ULift.{u} ℤ_[p.1]) ≃o ℕ∞ᵒᵈ :=
  ULift.ringEquiv.idealComapOrderIso.symm.trans
    (IsDiscreteValuationRing.idealOrderIsoENat ℤ_[p.1])

/-- The ordinary `ℕ∞` exponent of an ideal in an uplifted p-adic factor. -/
noncomputable def liftedPadicIdealExponent (p : Nat.Primes)
    (I : Ideal (ULift.{u} ℤ_[p.1])) : ℕ∞ :=
  OrderDual.ofDual (liftedPadicIdealOrderIso p I)

/-- The ideal in an uplifted p-adic factor having the prescribed exponent. -/
noncomputable def liftedPadicIdealOfExponent (p : Nat.Primes) (n : ℕ∞) :
    Ideal (ULift.{u} ℤ_[p.1]) :=
  (liftedPadicIdealOrderIso p).symm (OrderDual.toDual n)

/-- Recovering the exponent of the ideal constructed from it. -/
@[simp]
theorem liftedPadicIdealExponent_idealOfExponent
    (p : Nat.Primes) (n : ℕ∞) :
    liftedPadicIdealExponent p (liftedPadicIdealOfExponent p n) = n := by
  simp [liftedPadicIdealExponent, liftedPadicIdealOfExponent]

/-- Reconstructing an uplifted p-adic ideal from its exponent. -/
@[simp]
theorem liftedPadicIdealOfExponent_exponent
    (p : Nat.Primes) (I : Ideal (ULift.{u} ℤ_[p.1])) :
    liftedPadicIdealOfExponent p (liftedPadicIdealExponent p I) = I := by
  simp [liftedPadicIdealExponent, liftedPadicIdealOfExponent]

/-- A finite exponent gives the corresponding power of the maximal ideal,
transported along the `ULift` ring equivalence. -/
theorem liftedPadicIdealOfExponent_natCast (p : Nat.Primes) (n : ℕ) :
    liftedPadicIdealOfExponent p (n : ℕ∞) =
      (IsLocalRing.maximalIdeal ℤ_[p.1] ^ n).comap
        ULift.ringEquiv := by
  apply (liftedPadicIdealOrderIso p).injective
  simp [liftedPadicIdealOfExponent, liftedPadicIdealOrderIso,
    IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe]

/-- Exponent zero gives the unit ideal. -/
@[simp]
theorem liftedPadicIdealOfExponent_zero (p : Nat.Primes) :
    liftedPadicIdealOfExponent p 0 = ⊤ := by
  simpa using liftedPadicIdealOfExponent_natCast p 0

/-- Infinite exponent gives the zero ideal. -/
@[simp]
theorem liftedPadicIdealOfExponent_top (p : Nat.Primes) :
    liftedPadicIdealOfExponent p ⊤ = ⊥ := by
  apply (liftedPadicIdealOrderIso p).injective
  simp [liftedPadicIdealOfExponent]

/-- Every ideal in an uplifted p-adic factor is closed. -/
theorem isClosed_liftedPadicIdeal (p : Nat.Primes)
    (I : Ideal (ULift.{u} ℤ_[p.1])) :
    IsClosed (I : Set (ULift.{u} ℤ_[p.1])) := by
  have hmap : IsClosed
      ((I.map ULift.ringEquiv : Ideal ℤ_[p.1]) : Set ℤ_[p.1]) :=
    inferInstance
  rw [show (I : Set (ULift.{u} ℤ_[p.1])) =
      ULift.down ⁻¹' (I.map ULift.ringEquiv : Set ℤ_[p.1]) by
    ext x
    exact Ideal.apply_mem_of_equiv_iff.symm]
  exact hmap.preimage continuous_uliftDown

/-- The coordinatewise exponents of an ideal in the primewise p-adic ring. -/
noncomputable def primewisePadicIdealExponents
    (I : Ideal primewisePadicRing.{u}) (p : Nat.Primes) : ℕ∞ :=
  liftedPadicIdealExponent p
    (I.map (Pi.evalRingHom
      (fun q : Nat.Primes ↦ ULift.{u} ℤ_[q.1]) p))

/-- The product ideal having the prescribed primewise exponents. -/
noncomputable def primewisePadicIdealOfExponents
    (e : Nat.Primes → ℕ∞) : Ideal primewisePadicRing.{u} :=
  Ideal.pi (fun p ↦ liftedPadicIdealOfExponent p (e p))

/-- Membership in the ideal constructed from primewise exponents is
coordinatewise membership in the corresponding factor ideals. -/
@[simp]
theorem mem_primewisePadicIdealOfExponents
    (e : Nat.Primes → ℕ∞) (x : primewisePadicRing.{u}) :
    x ∈ primewisePadicIdealOfExponents e ↔
      ∀ p, x p ∈ liftedPadicIdealOfExponent p (e p) :=
  Iff.rfl

/-- A product ideal constructed from primewise exponents is closed. -/
theorem isClosed_primewisePadicIdealOfExponents
    (e : Nat.Primes → ℕ∞) :
    IsClosed ((primewisePadicIdealOfExponents e :
      Ideal primewisePadicRing.{u}) : Set primewisePadicRing.{u}) := by
  rw [show ((primewisePadicIdealOfExponents e :
      Ideal primewisePadicRing.{u}) : Set primewisePadicRing.{u}) =
      ⋂ p, {x | x p ∈ liftedPadicIdealOfExponent p (e p)} by
    ext x
    simp]
  exact isClosed_iInter fun p ↦
    (isClosed_liftedPadicIdeal p
      (liftedPadicIdealOfExponent p (e p))).preimage (continuous_apply p)

/-- Every closed ideal in the primewise p-adic ring is reconstructed from its
primewise exponents. -/
theorem eq_primewisePadicIdealOfExponents
    (I : Ideal primewisePadicRing.{u})
    (hI : IsClosed (I : Set primewisePadicRing.{u})) :
    I = primewisePadicIdealOfExponents (primewisePadicIdealExponents I) := by
  calc
    I = Ideal.pi (fun p ↦ I.map (Pi.evalRingHom
        (fun q : Nat.Primes ↦ ULift.{u} ℤ_[q.1]) p)) :=
      Ideal.eq_pi_map_evalRingHom_of_isClosed I hI
    _ = primewisePadicIdealOfExponents (primewisePadicIdealExponents I) := by
      unfold primewisePadicIdealOfExponents primewisePadicIdealExponents
      congr 1
      funext p
      exact (liftedPadicIdealOfExponent_exponent p _).symm

/-- The exponents of a product ideal are the exponents used to construct it. -/
@[simp]
theorem primewisePadicIdealExponents_idealOfExponents
    (e : Nat.Primes → ℕ∞) :
    primewisePadicIdealExponents
      (primewisePadicIdealOfExponents.{u} e) = e := by
  funext p
  unfold primewisePadicIdealExponents primewisePadicIdealOfExponents
  rw [Ideal.map_evalRingHom_pi]
  exact liftedPadicIdealExponent_idealOfExponent p (e p)

/-- Primewise exponents uniquely determine their product ideal. -/
theorem primewisePadicIdealOfExponents_injective :
    Function.Injective
      (primewisePadicIdealOfExponents.{u} :
        (Nat.Primes → ℕ∞) → Ideal primewisePadicRing.{u}) := by
  intro e f h
  simpa only [primewisePadicIdealExponents_idealOfExponents] using
    congrArg primewisePadicIdealExponents h

/-- Equality of ideals constructed from primewise exponents is exactly equality
of the exponent families. -/
@[simp]
theorem primewisePadicIdealOfExponents_inj
    {e f : Nat.Primes → ℕ∞} :
    primewisePadicIdealOfExponents.{u} e =
        primewisePadicIdealOfExponents f ↔ e = f :=
  primewisePadicIdealOfExponents_injective.eq_iff

/-- Constant exponent zero gives the top ideal in the primewise product. -/
@[simp]
theorem primewisePadicIdealOfExponents_zero :
    primewisePadicIdealOfExponents.{u} 0 = ⊤ := by
  ext x
  simp

/-- Constant infinite exponent gives the zero ideal in the primewise product. -/
@[simp]
theorem primewisePadicIdealOfExponents_top :
    primewisePadicIdealOfExponents.{u} ⊤ = ⊥ := by
  ext x
  simp only [mem_primewisePadicIdealOfExponents, Pi.top_apply,
    liftedPadicIdealOfExponent_top, Ideal.mem_bot]
  exact ⟨fun h ↦ funext h, fun h p ↦ congrFun h p⟩

end ProfiniteGrp
