/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups

/-!
# Primewise quotient clients

Downstream-client checks for the product-ideal quotient and primewise p-adic
factor-model APIs. Run in ordinary and -T0 modes with:

```
lake env lean -DwarningAsError=true Tests/PrimewisePadicQuotients.lean
lake env lean -T0 -DwarningAsError=true Tests/PrimewisePadicQuotients.lean
```
-/

@[expose] public section

universe u v

section Generic

variable {ι : Type u} {R : ι → Type v} [∀ i, CommRing (R i)]
variable (I : ∀ i, Ideal (R i))

example : Function.Surjective (Ideal.piQuotientMap I) :=
  Ideal.piQuotientMap_surjective I

example : RingHom.ker (Ideal.piQuotientMap I) = Ideal.pi I :=
  Ideal.ker_piQuotientMap I

example (x : ∀ i, R i) (i : ι) :
    Ideal.piQuotientRingEquiv I
        (Ideal.Quotient.mk (Ideal.pi I) x) i =
      Ideal.Quotient.mk (I i) (x i) := by
  simp

end Generic

section EmptyIndex

example : Function.Surjective
    (Ideal.piQuotientMap
      (R := fun _ : Empty ↦ ℤ) (fun _ ↦ (⊥ : Ideal ℤ))) :=
  Ideal.piQuotientMap_surjective _

end EmptyIndex

section Primewise

open ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

variable (p : Nat.Primes)

noncomputable example :
    (ULift.{0} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p (0 : ℕ∞)) ≃ₜ+
      ZMod 1 :=
  liftedPadicQuotientContinuousAddEquivZero p

noncomputable example :
    (ULift.{1} ℤ_[p.1] ⧸
      liftedPadicIdealOfExponent p ((2 : ℕ) : ℕ∞)) ≃+*
      ZMod (p.1 ^ 2) :=
  liftedPadicQuotientRingEquivZMod p 2

noncomputable example :
    (ULift.{1} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p ⊤) ≃ₜ+
      ULift.{1} ℤ_[p.1] :=
  liftedPadicQuotientContinuousAddEquivTop p

example (x : ULift.{1} ℤ_[p.1]) :
    liftedPadicQuotientRingEquivZMod p 2
        (Ideal.Quotient.mk
          (liftedPadicIdealOfExponent p ((2 : ℕ) : ℕ∞)) x) =
      PadicInt.toZModPow 2 x.down := by
  exact liftedPadicQuotientRingEquivZMod_mk p 2 x

example (e : ℕ∞)
    (x : ULift.{1} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p e) :
    (liftedPadicQuotientContinuousAddEquivFactor p e).symm
        (liftedPadicQuotientContinuousAddEquivFactor p e x) = x := by
  simp

/-- A shared quotient profile: zero at two, finite at three, top otherwise. -/
noncomputable def mixedExponents (q : Nat.Primes) : ℕ∞ :=
  if q.1 = 2 then 0 else if q.1 = 3 then 2 else ⊤

noncomputable example :
    (primewisePadicRing.{1} ⧸ primewisePadicIdealOfExponents (fun _ ↦ 0))
      ≃ₜ+ primewisePadicQuotientModel (fun _ ↦ 0) :=
  primewisePadicQuotientContinuousAddEquivModel _

noncomputable example :
    (primewisePadicRing.{1} ⧸ primewisePadicIdealOfExponents (fun _ ↦ ⊤))
      ≃ₜ+ primewisePadicQuotientModel (fun _ ↦ ⊤) :=
  primewisePadicQuotientContinuousAddEquivModel _

noncomputable example :
    (primewisePadicRing.{1} ⧸ primewisePadicIdealOfExponents mixedExponents)
      ≃ₜ+ primewisePadicQuotientModel mixedExponents :=
  primewisePadicQuotientContinuousAddEquivModel mixedExponents

example (x : primewisePadicRing.{1}) (q : Nat.Primes) :
    primewisePadicQuotientContinuousAddEquivModel mixedExponents
        (Ideal.Quotient.mk (primewisePadicIdealOfExponents mixedExponents) x) q =
      liftedPadicQuotientContinuousAddEquivFactor q (mixedExponents q)
        (Ideal.Quotient.mk
          (liftedPadicIdealOfExponent q (mixedExponents q)) (x q)) := by
  simp

end Primewise
