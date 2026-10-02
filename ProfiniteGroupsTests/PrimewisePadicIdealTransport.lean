/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups

/-!
# Primewise ideal transport clients

Proof-using downstream checks for universe-change ring equivalences, coordinate
images of arbitrary ideals, and zero/finite/infinite factor and mixed-product
exponents. Run both in ordinary and `-T0` modes.
-/

@[expose] public section

open ProfiniteGrp

universe u v w

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private def twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
private def threePrime : Nat.Primes := ⟨3, Nat.prime_three⟩
private def fivePrime : Nat.Primes := ⟨5, Nat.prime_five⟩

private def mixedExponents (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then 0 else if p.1 = 3 then 2 else ⊤

example : mixedExponents twoPrime = 0 := by simp [mixedExponents, twoPrime]
example : mixedExponents threePrime = (2 : ℕ∞) := by
  simp [mixedExponents, threePrime]
example : mixedExponents fivePrime = ⊤ := by simp [mixedExponents, fivePrime]
example : mixedExponents threePrime ≠ mixedExponents twoPrime := by
  simp [mixedExponents, threePrime, twoPrime]
example : mixedExponents threePrime ≠ mixedExponents fivePrime := by
  simp [mixedExponents, threePrime, fivePrime]

section Generic

private noncomputable def integerChange : ULift.{u} ℤ ≃+* ULift.{v} ℤ :=
  ULift.ringEquiv.trans ULift.ringEquiv.symm

private theorem boolCoordinateImage (I : Ideal (Bool → ULift.{v} ℤ)) (i : Bool) :
    (I.comap (RingEquiv.piCongrRight (fun _ : Bool ↦ integerChange.{u,v}))).map
        (Pi.evalRingHom (fun _ : Bool ↦ ULift.{u} ℤ) i) =
      (I.map (Pi.evalRingHom (fun _ : Bool ↦ ULift.{v} ℤ) i)).comap
        integerChange.{u,v} :=
  Ideal.map_evalRingHom_comap_piCongrRight _ I i

private theorem emptyCoordinateImage (I : Ideal (Empty → ULift.{v} ℤ)) (i : Empty) :
    (I.comap (RingEquiv.piCongrRight (fun _ : Empty ↦ integerChange.{u,v}))).map
        (Pi.evalRingHom (fun _ : Empty ↦ ULift.{u} ℤ) i) =
      (I.map (Pi.evalRingHom (fun _ : Empty ↦ ULift.{v} ℤ) i)).comap
        integerChange.{u,v} :=
  Ideal.map_evalRingHom_comap_piCongrRight _ I i

end Generic

section Factor

variable (p : Nat.Primes) (x : ULift.{u} ℤ_[p.1])

example : (liftedPadicChangeUniverseRingEquiv.{u,v} p x).down = x.down := by
  simp

example : (liftedPadicChangeUniverseRingEquiv.{u,v} p).symm
      (liftedPadicChangeUniverseRingEquiv.{u,v} p x) = x := by
  exact (liftedPadicChangeUniverseRingEquiv.{u,v} p).symm_apply_apply x

example : (liftedPadicChangeUniverseRingEquiv.{u,v} p).trans
    (liftedPadicChangeUniverseRingEquiv.{v,w} p) x =
      liftedPadicChangeUniverseRingEquiv.{u,w} p x := by
  rw [liftedPadicChangeUniverseRingEquiv_trans]

example : liftedPadicChangeUniverseRingEquiv.{u,u} p x = x := by simp

example (I : Ideal (ULift.{v} ℤ_[p.1])) :
    liftedPadicIdealExponent p
      (I.comap (liftedPadicChangeUniverseRingEquiv.{u,v} p)) =
        liftedPadicIdealExponent p I :=
  liftedPadicIdealExponent_comap_changeUniverse p I

private theorem factorMapExponent (I : Ideal (ULift.{u} ℤ_[p.1])) :
    liftedPadicIdealExponent p
      (I.map (liftedPadicChangeUniverseRingEquiv.{u,v} p)) =
        liftedPadicIdealExponent p I :=
  liftedPadicIdealExponent_map_changeUniverse p I

private theorem factorTopExponent : liftedPadicIdealExponent p
    ((⊤ : Ideal (ULift.{v} ℤ_[p.1])).comap
      (liftedPadicChangeUniverseRingEquiv.{u,v} p)) = 0 := by
  rw [liftedPadicIdealExponent_comap_changeUniverse,
    ← liftedPadicIdealOfExponent_zero p,
    liftedPadicIdealExponent_idealOfExponent]

private theorem factorBottomExponent : liftedPadicIdealExponent p
    ((⊥ : Ideal (ULift.{v} ℤ_[p.1])).comap
      (liftedPadicChangeUniverseRingEquiv.{u,v} p)) = ⊤ := by
  rw [liftedPadicIdealExponent_comap_changeUniverse,
    ← liftedPadicIdealOfExponent_top p,
    liftedPadicIdealExponent_idealOfExponent]

private theorem factorFiniteExponent : liftedPadicIdealExponent p
    ((IsLocalRing.maximalIdeal ℤ_[p.1] ^ 2).comap
      (ULift.ringEquiv : ULift.{v} ℤ_[p.1] ≃+* ℤ_[p.1]) |>.comap
        (liftedPadicChangeUniverseRingEquiv.{u,v} p)) = (2 : ℕ∞) := by
  rw [liftedPadicIdealExponent_comap_changeUniverse,
    ← liftedPadicIdealOfExponent_natCast p 2,
    liftedPadicIdealExponent_idealOfExponent]
  rfl

example (n : ℕ∞) :
    (liftedPadicIdealOfExponent.{v} p n).comap
        (liftedPadicChangeUniverseRingEquiv.{u,v} p) =
      liftedPadicIdealOfExponent.{u} p n := by
  exact liftedPadicIdealOfExponent_comap_changeUniverse p n

end Factor

section Product

variable (I : Ideal primewisePadicRing.{v}) (x : primewisePadicRing.{u})

private theorem productCoordinateImage (p : Nat.Primes) :
    (primewisePadicRingChangeUniverse.{u,v} x p).down = (x p).down := by
  simp

example (n : ℤ) :
    primewisePadicRingChangeUniverse.{u,v}
        (n : primewisePadicRing.{u}) = (n : primewisePadicRing.{v}) := by
  simp

example : primewisePadicRingChangeUniverse.{u,u} x = x := by simp

example : primewisePadicRingChangeUniverse.{u,v}.symm
    (primewisePadicRingChangeUniverse.{u,v} x) = x := by
  exact primewisePadicRingChangeUniverse.{u,v}.symm_apply_apply x

example : primewisePadicRingChangeUniverse.{u,v}.trans
    primewisePadicRingChangeUniverse.{v,w} x =
      primewisePadicRingChangeUniverse.{u,w} x := by
  rw [primewisePadicRingChangeUniverse_trans]

example (p : Nat.Primes) :
    (I.comap primewisePadicRingChangeUniverse.{u,v}).map
        (Pi.evalRingHom (fun q : Nat.Primes ↦ ULift.{u} ℤ_[q.1]) p) =
      (I.map (Pi.evalRingHom
        (fun q : Nat.Primes ↦ ULift.{v} ℤ_[q.1]) p)).comap
          (liftedPadicChangeUniverseRingEquiv.{u,v} p) := by
  exact Ideal.map_evalRingHom_comap_piCongrRight _ I p

private theorem productComapExponent : primewisePadicIdealExponents
    (I.comap primewisePadicRingChangeUniverse.{u,v}) =
      primewisePadicIdealExponents I :=
  primewisePadicIdealExponents_comap_changeUniverse I

example (J : Ideal primewisePadicRing.{u}) : primewisePadicIdealExponents
    (J.map primewisePadicRingChangeUniverse.{u,v}) =
      primewisePadicIdealExponents J :=
  primewisePadicIdealExponents_map_changeUniverse J

example : (primewisePadicIdealOfExponents.{v} mixedExponents).comap
    primewisePadicRingChangeUniverse.{u,v} =
      primewisePadicIdealOfExponents.{u} mixedExponents := by
  simp

private theorem mixedZeroExponent : primewisePadicIdealExponents
    ((primewisePadicIdealOfExponents.{v} mixedExponents).comap
      primewisePadicRingChangeUniverse.{u,v}) twoPrime = 0 := by
  rw [primewisePadicIdealExponents_comap_changeUniverse,
    primewisePadicIdealExponents_idealOfExponents]
  simp [mixedExponents, twoPrime]

private theorem mixedFiniteExponent : primewisePadicIdealExponents
    ((primewisePadicIdealOfExponents.{v} mixedExponents).comap
      primewisePadicRingChangeUniverse.{u,v}) threePrime = 2 := by
  rw [primewisePadicIdealExponents_comap_changeUniverse,
    primewisePadicIdealExponents_idealOfExponents]
  simp [mixedExponents, threePrime]

private theorem mixedInfiniteExponent : primewisePadicIdealExponents
    ((primewisePadicIdealOfExponents.{v} mixedExponents).comap
      primewisePadicRingChangeUniverse.{u,v}) fivePrime = ⊤ := by
  rw [primewisePadicIdealExponents_comap_changeUniverse,
    primewisePadicIdealExponents_idealOfExponents]
  simp [mixedExponents, fivePrime]

end Product

private theorem mixedNotTop : primewisePadicIdealOfExponents.{u} mixedExponents ≠ ⊤ := by
  intro heq
  have hOne : (1 : primewisePadicRing.{u}) ∈
      primewisePadicIdealOfExponents mixedExponents := by
    rw [heq]
    trivial
  have hFive := (mem_primewisePadicIdealOfExponents mixedExponents _).mp hOne fivePrime
  have hTop : mixedExponents fivePrime = ⊤ := by
    simp [mixedExponents, fivePrime]
  rw [hTop, liftedPadicIdealOfExponent_top] at hFive
  exact one_ne_zero (by simpa only [Pi.one_apply, Ideal.mem_bot] using hFive)

private theorem mixedNotBottom : primewisePadicIdealOfExponents.{u} mixedExponents ≠ ⊥ := by
  intro heq
  have h := congrFun (congrArg primewisePadicIdealExponents heq) twoPrime
  rw [← primewisePadicIdealOfExponents_top,
    primewisePadicIdealExponents_idealOfExponents,
    primewisePadicIdealExponents_idealOfExponents] at h
  simp only [Pi.top_apply] at h
  norm_num [mixedExponents, twoPrime] at h

example (I : Ideal primewisePadicRing.{1}) :
    primewisePadicIdealExponents
        (I.comap primewisePadicRingChangeUniverse.{0,1}) =
      primewisePadicIdealExponents I :=
  primewisePadicIdealExponents_comap_changeUniverse I

example (I : Ideal primewisePadicRing.{0}) :
    primewisePadicIdealExponents
        (I.comap primewisePadicRingChangeUniverse.{1,0}) =
      primewisePadicIdealExponents I :=
  primewisePadicIdealExponents_comap_changeUniverse I
