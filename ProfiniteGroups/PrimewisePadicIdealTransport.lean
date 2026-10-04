/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.PrimewisePadicIdeals

/-!
# Changing the universe of primewise p-adic ideals

The coordinate-preserving ring equivalence between universe lifts of the
p-adic integers preserves the exponent of every factor ideal. Coordinate
images then show that it also preserves the exponent family of every ideal
in the primewise product, without a closedness hypothesis. Only closed ideals
are reconstructed from their exponent families.

## References

- Mathlib, `ULift.ringEquiv`, `Ideal.map` and `Ideal.comap` for changing the
  universe of p-adic factor ideals; `PrimewisePadicIdeals` supplies exponents.
-/

@[expose] public section

universe u v w

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Change only the `ULift` universe of a p-adic factor. -/
noncomputable def liftedPadicChangeUniverseRingEquiv (p : Nat.Primes) :
    ULift.{u} ℤ_[p.1] ≃+* ULift.{v} ℤ_[p.1] :=
  ULift.ringEquiv.trans ULift.ringEquiv.symm

/-- Changing universes preserves the underlying p-adic integer. -/
@[simp]
theorem liftedPadicChangeUniverseRingEquiv_down (p : Nat.Primes)
    (x : ULift.{u} ℤ_[p.1]) :
    (liftedPadicChangeUniverseRingEquiv.{u,v} p x).down = x.down :=
  rfl

/-- Changing a factor's universe to itself is the identity. -/
@[simp]
theorem liftedPadicChangeUniverseRingEquiv_self (p : Nat.Primes) :
    liftedPadicChangeUniverseRingEquiv.{u,u} p = RingEquiv.refl _ := by
  ext x
  cases x
  rfl

/-- Reversing the change of universe exchanges its endpoints. -/
@[simp]
theorem liftedPadicChangeUniverseRingEquiv_symm (p : Nat.Primes) :
    (liftedPadicChangeUniverseRingEquiv.{u,v} p).symm =
      liftedPadicChangeUniverseRingEquiv.{v,u} p := by
  ext x
  cases x
  rfl

/-- Successive factor universe changes compose directly. -/
@[simp]
theorem liftedPadicChangeUniverseRingEquiv_trans (p : Nat.Primes) :
    (liftedPadicChangeUniverseRingEquiv.{u,v} p).trans
      (liftedPadicChangeUniverseRingEquiv.{v,w} p) =
        liftedPadicChangeUniverseRingEquiv.{u,w} p := by
  ext x
  cases x
  rfl

/-- Change the universe of each factor of the primewise p-adic product ring. -/
noncomputable def primewisePadicRingChangeUniverse :
    primewisePadicRing.{u} ≃+* primewisePadicRing.{v} :=
  RingEquiv.piCongrRight (fun p ↦ liftedPadicChangeUniverseRingEquiv.{u,v} p)

/-- The product equivalence acts by the factor equivalence at each prime. -/
@[simp]
theorem primewisePadicRingChangeUniverse_apply
    (x : primewisePadicRing.{u}) (p : Nat.Primes) :
    primewisePadicRingChangeUniverse.{u,v} x p =
      liftedPadicChangeUniverseRingEquiv.{u,v} p (x p) :=
  rfl

/-- Each coordinate retains its underlying p-adic integer. -/
@[simp]
theorem primewisePadicRingChangeUniverse_down
    (x : primewisePadicRing.{u}) (p : Nat.Primes) :
    (primewisePadicRingChangeUniverse.{u,v} x p).down = (x p).down :=
  rfl

/-- The product ring equivalence preserves the integral diagonal. -/
theorem primewisePadicRingChangeUniverse_intCast (n : ℤ) :
    primewisePadicRingChangeUniverse.{u,v} (n : primewisePadicRing.{u}) =
      (n : primewisePadicRing.{v}) :=
  map_intCast _ _

/-- Changing the product ring's universe to itself is the identity. -/
@[simp]
theorem primewisePadicRingChangeUniverse_self :
    primewisePadicRingChangeUniverse.{u,u} = RingEquiv.refl _ := by
  simp [primewisePadicRingChangeUniverse]

/-- Reversing the product equivalence exchanges its universe endpoints. -/
@[simp]
theorem primewisePadicRingChangeUniverse_symm :
    (primewisePadicRingChangeUniverse.{u,v}).symm =
      primewisePadicRingChangeUniverse.{v,u} := by
  simp [primewisePadicRingChangeUniverse]

/-- Successive changes of product universe compose directly. -/
@[simp]
theorem primewisePadicRingChangeUniverse_trans :
    primewisePadicRingChangeUniverse.{u,v}.trans
      primewisePadicRingChangeUniverse.{v,w} =
        primewisePadicRingChangeUniverse.{u,w} := by
  simp [primewisePadicRingChangeUniverse]

/-- Every factor ideal has the same exponent after changing its `ULift` universe. -/
theorem liftedPadicIdealExponent_comap_changeUniverse (p : Nat.Primes)
    (I : Ideal (ULift.{v} ℤ_[p.1])) :
    liftedPadicIdealExponent p
      (I.comap (liftedPadicChangeUniverseRingEquiv.{u,v} p)) =
        liftedPadicIdealExponent p I := by
  have hmap :
      (I.comap (liftedPadicChangeUniverseRingEquiv.{u,v} p)).map
        (ULift.ringEquiv : ULift.{u} ℤ_[p.1] ≃+* ℤ_[p.1]) =
      I.map (ULift.ringEquiv : ULift.{v} ℤ_[p.1] ≃+* ℤ_[p.1]) := by
    rw [← Ideal.map_symm (liftedPadicChangeUniverseRingEquiv.{u,v} p)]
    change (I.map (liftedPadicChangeUniverseRingEquiv.{u,v} p).symm.toRingHom).map
      (ULift.ringEquiv : ULift.{u} ℤ_[p.1] ≃+* ℤ_[p.1]).toRingHom = _
    calc
      _ = I.map ((ULift.ringEquiv : ULift.{u} ℤ_[p.1] ≃+* ℤ_[p.1]).toRingHom.comp
          (liftedPadicChangeUniverseRingEquiv.{u,v} p).symm.toRingHom) :=
        I.map_map _ _
      _ = _ := congrArg (I.map ·) (RingHom.ext fun x ↦ rfl)
  change OrderDual.ofDual ((IsDiscreteValuationRing.idealOrderIsoENat ℤ_[p.1])
      ((I.comap (liftedPadicChangeUniverseRingEquiv.{u,v} p)).map
        (ULift.ringEquiv : ULift.{u} ℤ_[p.1] ≃+* ℤ_[p.1]))) =
    OrderDual.ofDual ((IsDiscreteValuationRing.idealOrderIsoENat ℤ_[p.1])
      (I.map (ULift.ringEquiv : ULift.{v} ℤ_[p.1] ≃+* ℤ_[p.1])))
  rw [hmap]

/-- The equivalent forward image also preserves a factor ideal's exponent. -/
theorem liftedPadicIdealExponent_map_changeUniverse (p : Nat.Primes)
    (I : Ideal (ULift.{u} ℤ_[p.1])) :
    liftedPadicIdealExponent p
      (I.map (liftedPadicChangeUniverseRingEquiv.{u,v} p)) =
        liftedPadicIdealExponent p I := by
  exact (congrArg (liftedPadicIdealExponent p)
    (Ideal.map_comap_of_equiv (liftedPadicChangeUniverseRingEquiv.{u,v} p))).trans
      (by simpa only [liftedPadicChangeUniverseRingEquiv_symm] using
        liftedPadicIdealExponent_comap_changeUniverse.{v,u} p I)

/-- Forming an uplifted factor ideal commutes with coordinate-preserving comap. -/
@[simp]
theorem liftedPadicIdealOfExponent_comap_changeUniverse (p : Nat.Primes)
    (n : ℕ∞) :
    (liftedPadicIdealOfExponent.{v} p n).comap
        (liftedPadicChangeUniverseRingEquiv.{u,v} p) =
      liftedPadicIdealOfExponent.{u} p n := by
  calc
    _ = liftedPadicIdealOfExponent.{u} p
        (liftedPadicIdealExponent p
          ((liftedPadicIdealOfExponent.{v} p n).comap
            (liftedPadicChangeUniverseRingEquiv.{u,v} p))) :=
      (liftedPadicIdealOfExponent_exponent p _).symm
    _ = _ := by
      rw [liftedPadicIdealExponent_comap_changeUniverse,
        liftedPadicIdealExponent_idealOfExponent]

end ProfiniteGrp

namespace Ideal

/-- Evaluation of the coordinate image commutes with comap of a
coordinatewise ring equivalence, without a closedness assumption. -/
theorem map_evalRingHom_comap_piCongrRight
    {ι : Type*} {R S : ι → Type*} [∀ i, Semiring (R i)] [∀ i, Semiring (S i)]
    (e : ∀ i, R i ≃+* S i) (I : Ideal (∀ i, S i)) (i : ι) :
    (I.comap (RingEquiv.piCongrRight e)).map (Pi.evalRingHom R i) =
      (I.map (Pi.evalRingHom S i)).comap (e i) := by
  calc
    _ = I.map ((Pi.evalRingHom R i).comp
          (RingEquiv.piCongrRight e).symm.toRingHom) := by
      rw [← Ideal.map_symm (RingEquiv.piCongrRight e)]
      change (I.map (RingEquiv.piCongrRight e).symm.toRingHom).map
        (Pi.evalRingHom R i) = _
      exact I.map_map _ _
    _ = I.map ((e i).symm.toRingHom.comp (Pi.evalRingHom S i)) := by
      congr 1
    _ = _ := by
      rw [← Ideal.map_symm (e i)]
      exact (I.map_map _ _).symm

end Ideal

namespace ProfiniteGrp

/-- Every ideal in the product has universe-independent coordinate exponents;
closedness is not required because only coordinate images are compared. -/
theorem primewisePadicIdealExponents_comap_changeUniverse
    (I : Ideal primewisePadicRing.{v}) :
    primewisePadicIdealExponents
      (I.comap primewisePadicRingChangeUniverse.{u,v}) =
        primewisePadicIdealExponents I := by
  funext p
  unfold primewisePadicIdealExponents
  rw [primewisePadicRingChangeUniverse]
  rw [Ideal.map_evalRingHom_comap_piCongrRight]
  exact liftedPadicIdealExponent_comap_changeUniverse.{u,v} p _

/-- The forward image of an arbitrary product ideal has the same exponents. -/
theorem primewisePadicIdealExponents_map_changeUniverse
    (I : Ideal primewisePadicRing.{u}) :
    primewisePadicIdealExponents
      (I.map primewisePadicRingChangeUniverse.{u,v}) =
        primewisePadicIdealExponents I := by
  exact (congrArg primewisePadicIdealExponents
    (Ideal.map_comap_of_equiv primewisePadicRingChangeUniverse.{u,v})).trans
      (by simpa only [primewisePadicRingChangeUniverse_symm] using
        primewisePadicIdealExponents_comap_changeUniverse.{v,u} I)

/-- The product ideal made from exponents commutes with changing universes. -/
@[simp]
theorem primewisePadicIdealOfExponents_comap_changeUniverse
    (e : Nat.Primes → ℕ∞) :
    (primewisePadicIdealOfExponents.{v} e).comap
        primewisePadicRingChangeUniverse.{u,v} =
      primewisePadicIdealOfExponents.{u} e := by
  ext x
  change (∀ p, (liftedPadicChangeUniverseRingEquiv.{u,v} p (x p)) ∈
      liftedPadicIdealOfExponent.{v} p (e p)) ↔
    ∀ p, x p ∈ liftedPadicIdealOfExponent.{u} p (e p)
  simp only [← Ideal.mem_comap, liftedPadicIdealOfExponent_comap_changeUniverse]

end ProfiniteGrp
