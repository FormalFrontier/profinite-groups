/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicRealization

/-!
# Primewise realization clients

Public proof-use clients for arbitrary, zero, infinite, finite, and mixed profiles.
-/

@[expose] public section

open ProfiniteGrp

universe u v

namespace ProcyclicRealizationTests

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem arbitraryMap (e : Nat.Primes → ℕ∞) :
    Function.Surjective (primewisePadicRealizationMap.{u} e) :=
  primewisePadicRealizationMap_surjective e

theorem arbitraryActualKernel (e : Nat.Primes → ℕ∞) :
    primewisePadicKernelIdeal (primewisePadicRealizationMap.{u} e) =
      primewisePadicIdealOfExponents.{u} e :=
  primewisePadicKernelIdeal_realizationMap e

theorem arbitraryExtractedKernel (e : Nat.Primes → ℕ∞) :
    primewisePadicKernelExponents (primewisePadicRealizationMap.{u} e) = e :=
  primewisePadicKernelExponents_realizationMap e

theorem arbitraryRepresentative (e : Nat.Primes → ℕ∞)
    (x : primewisePadicRing.{u}) (p : Nat.Primes) :
    ((primewisePadicRealizationMap e
      (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x))).toAdd) p =
      liftedPadicQuotientContinuousAddEquivFactor p (e p)
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p (e p)) (x p)) :=
  primewisePadicRealizationMap_apply_coordinate e x p

theorem arbitraryGenerator (e : Nat.Primes → ℕ∞) :
    IsTopologicalGenerator (primewisePadicProcyclicModel.{u} e)
      (primewisePadicRealizationGenerator e) :=
  primewisePadicRealizationGenerator_isTopologicalGenerator e

theorem arbitraryInvariant (e : Nat.Primes → ℕ∞)
    (h : IsProcyclic (primewisePadicProcyclicModel.{u} e)) :
    h.exponents = e :=
  primewisePadicProcyclicModel_exponents e h

theorem arbitraryPositiveUniverseExists (e : Nat.Primes → ℕ∞) :
    ∃ (G : ProfiniteGrp.{1}) (hG : IsProcyclic G), hG.exponents = e :=
  exists_procyclic_of_exponents e

theorem arbitraryIndependentUniverseEquiv (e f : Nat.Primes → ℕ∞) :
    Nonempty (primewisePadicProcyclicModel.{1} e ≃ₜ*
      primewisePadicProcyclicModel.{2} f) ↔ e = f :=
  primewisePadicProcyclicModel_nonempty_equiv_iff e f

theorem allZeroKernel :
    primewisePadicKernelIdeal
      (primewisePadicRealizationMap.{1} (fun _ => (0 : ℕ∞))) = ⊤ := by
  rw [primewisePadicKernelIdeal_realizationMap]
  exact primewisePadicIdealOfExponents_zero

theorem allZeroInvariant :
    (primewisePadicProcyclicModel_isProcyclic.{1} (fun _ => (0 : ℕ∞))).exponents =
      (fun _ => (0 : ℕ∞)) :=
  primewisePadicProcyclicModel_exponents _ _

theorem allZeroTrivial (x : primewisePadicProcyclicModel.{1} (fun _ => (0 : ℕ∞))) :
    x = 1 := by
  obtain ⟨y, rfl⟩ :=
    (primewisePadicRealizationMap_surjective.{1} (fun _ => (0 : ℕ∞))) x
  let representative := (primewisePadicRingMultiplicativeEquiv.{1}.symm y).toAdd
  have hk : representative ∈ primewisePadicKernelIdeal
      (primewisePadicRealizationMap.{1} (fun _ => (0 : ℕ∞))) := by
    rw [allZeroKernel]
    trivial
  have heq := (mem_primewisePadicKernelIdeal _ representative).mp hk
  change (primewisePadicRealizationMap (fun _ => (0 : ℕ∞)))
    (primewisePadicRingMultiplicativeEquiv
      (primewisePadicRingMultiplicativeEquiv.symm y)) = 1 at heq
  simpa only [ContinuousMulEquiv.apply_symm_apply] using heq

theorem allTopInvariant :
    (primewisePadicProcyclicModel_isProcyclic.{2} (fun _ => (⊤ : ℕ∞))).exponents =
      (fun _ => (⊤ : ℕ∞)) :=
  primewisePadicProcyclicModel_exponents _ _

theorem allTopGeneratorCoordinate (p : Nat.Primes) :
    (primewisePadicRealizationGenerator.{1} (fun _ => (⊤ : ℕ∞))).toAdd p =
      ULift.up (1 : ℤ_[p.1]) := by
  exact eq_of_heq
    (primewisePadicRealizationMap_diagonal_top_coordinate.{1}
      (fun _ => (⊤ : ℕ∞)) 1 p rfl)

theorem allTopGeneratorNotIdentity :
    primewisePadicRealizationGenerator.{1} (fun _ => (⊤ : ℕ∞)) ≠ 1 := by
  let two : Nat.Primes := ⟨2, by decide⟩
  intro h
  have hc := congrArg
    (fun x : primewisePadicProcyclicModel.{1} (fun _ => (⊤ : ℕ∞)) => x.toAdd two) h
  rw [allTopGeneratorCoordinate] at hc
  have h01 : (1 : ℤ_[2]) = 0 := congrArg ULift.down hc
  exact one_ne_zero h01

theorem positiveFiniteGeneratorCoordinate (p : Nat.Primes) :
    (primewisePadicRealizationGenerator.{1} (fun _ => (2 : ℕ∞))).toAdd p =
      ULift.up (1 : ZMod (p.1 ^ 2)) := by
  change ((primewisePadicRealizationMap.{1} (fun _ => (2 : ℕ∞))
    (primewisePadicDiagonal 1)).toAdd p) = _
  simpa only [map_one, Int.cast_one] using
    (eq_of_heq (primewisePadicRealizationMap_diagonal_natCast_coordinate.{1}
      (fun _ => (2 : ℕ∞)) 1 p 2 rfl))

theorem positiveFiniteInvariant :
    (primewisePadicProcyclicModel_isProcyclic.{1} (fun _ => (2 : ℕ∞))).exponents =
      (fun _ => (2 : ℕ∞)) :=
  primewisePadicProcyclicModel_exponents _ _

theorem positiveFiniteGeneratorNotIdentity :
    primewisePadicRealizationGenerator.{1} (fun _ => (2 : ℕ∞)) ≠ 1 := by
  let three : Nat.Primes := ⟨3, by decide⟩
  intro h
  have hc := congrArg
    (fun x : primewisePadicProcyclicModel.{1} (fun _ => (2 : ℕ∞)) => x.toAdd three) h
  rw [positiveFiniteGeneratorCoordinate] at hc
  have h01 : (1 : ZMod (3 ^ 2)) = 0 := congrArg ULift.down hc
  exact (by decide : (1 : ZMod (3 ^ 2)) ≠ 0) h01

/-- A realization profile combining zero, positive finite and top coordinates. -/
def mixed (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then 0 else if p.1 = 3 then 2 else ⊤

theorem mixedValues :
    mixed ⟨2, by decide⟩ = 0 ∧
      mixed ⟨3, by decide⟩ = 2 ∧
      mixed ⟨5, by decide⟩ = ⊤ := by
  simp [mixed]

theorem mixedZeroCoordinate :
    HEq ((primewisePadicRealizationMap.{1} mixed (primewisePadicDiagonal 1)).toAdd
      ⟨2, by decide⟩) (ULift.up (1 : ZMod (2 ^ 0))) := by
  simpa only [map_one, Int.cast_one] using
    (primewisePadicRealizationMap_diagonal_natCast_coordinate.{1}
      mixed 1 ⟨2, by decide⟩ 0 (by simp [mixed]))

theorem mixedFiniteCoordinate :
    HEq ((primewisePadicRealizationMap.{1} mixed (primewisePadicDiagonal 1)).toAdd
      ⟨3, by decide⟩) (ULift.up (1 : ZMod (3 ^ 2))) := by
  simpa only [map_one, Int.cast_one] using
    (primewisePadicRealizationMap_diagonal_natCast_coordinate.{1}
      mixed 1 ⟨3, by decide⟩ 2 (by simp [mixed]))

theorem mixedTopCoordinate :
    HEq ((primewisePadicRealizationMap.{1} mixed (primewisePadicDiagonal 1)).toAdd
      ⟨5, by decide⟩) (ULift.up (1 : ℤ_[5])) := by
  exact primewisePadicRealizationMap_diagonal_top_coordinate.{1}
    mixed 1 ⟨5, by decide⟩ (by simp [mixed])

theorem mixedInvariant :
    (primewisePadicProcyclicModel_isProcyclic.{1} mixed).exponents = mixed :=
  primewisePadicProcyclicModel_exponents mixed _

theorem unequalProfilesNoEquiv :
    ¬ Nonempty (primewisePadicProcyclicModel.{1} mixed ≃ₜ*
        primewisePadicProcyclicModel.{2} (fun _ => (⊤ : ℕ∞))) := by
  intro h
  have he := (primewisePadicProcyclicModel_nonempty_equiv_iff mixed _).mp h
  have h2 := congrFun he (⟨2, by decide⟩ : Nat.Primes)
  simp [mixed] at h2

end ProcyclicRealizationTests
