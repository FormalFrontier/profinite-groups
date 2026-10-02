/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicHom
public import ProfiniteGroups.ProcyclicPower
public import ProfiniteGroups.ProcyclicRealization

/-!
# Direct-leaf consumers

Import only the needed leaves: compare zero and one power images, a positive
power's finite quotient, and the actual kernel of a mixed realization map.
-/

@[expose] public section

open ProfiniteGrp

universe u

namespace DirectImportsTests

/-- Power zero gives the bottom subgroup; power one gives the whole group. -/
theorem zeroOnePowerImages (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) :
    (powerImage G hG 0 : Subgroup G) = ⊥ ∧
      (powerImage G hG 1 : Subgroup G) = ⊤ :=
  ⟨powerImage_zero G hG, powerImage_one G hG⟩

/-- A positive exponent gives a finite cyclic quotient and an open image. -/
theorem positivePowerQuotient (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (g : G) (hg : IsTopologicalGenerator G g) (n : ℕ) (hn : 0 < n) :
    IsOpen ((powerImage G hG n : Subgroup G) : Set G) ∧
      IsCyclic (G ⧸ (powerImage G hG n : Subgroup G)) ∧
      Finite (G ⧸ (powerImage G hG n : Subgroup G)) ∧
      (powerImage G hG n : Subgroup G).index ∣ n :=
  ⟨powerImage_isOpen G hG n hn,
   powerImage_quotient_isCyclic G hG g hg n hn,
   powerImage_quotient_finite G hG n hn,
   powerImage_index_dvd G hG n hn⟩

/-- The fourth-power image in the finite cyclic group of order twelve is open. -/
theorem cyclicTwelvePositivePower :
    IsOpen ((powerImage (finiteCyclic 12) (finiteCyclic_isProcyclic 12) 4 :
      Subgroup (finiteCyclic 12)) : Set (finiteCyclic 12)) ∧
      (powerImage (finiteCyclic 12) (finiteCyclic_isProcyclic 12) 4 :
        Subgroup (finiteCyclic 12)).index ∣ 4 :=
  ⟨powerImage_isOpen _ _ 4 (by decide), powerImage_index_dvd _ _ 4 (by decide)⟩

/-- A profile for the actual ideal-kernel check, with all three exponent regimes. -/
def mixedProfile (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then 0 else if p.1 = 3 then 2 else ⊤

/-- The realization map's actual ideal kernel is the prescribed mixed ideal. -/
theorem actualMixedKernel :
    primewisePadicKernelIdeal
      (primewisePadicRealizationMap.{u} mixedProfile) =
        primewisePadicIdealOfExponents mixedProfile :=
  primewisePadicKernelIdeal_realizationMap mixedProfile

/-- Both extreme profiles are recovered using only the realization leaf. -/
theorem zeroTopExtracted :
    primewisePadicKernelExponents
      (primewisePadicRealizationMap.{1} (fun _ => (0 : ℕ∞))) =
        (fun _ => (0 : ℕ∞)) ∧
    primewisePadicKernelExponents
      (primewisePadicRealizationMap.{1} (fun _ => (⊤ : ℕ∞))) =
        (fun _ => (⊤ : ℕ∞)) :=
  ⟨primewisePadicKernelExponents_realizationMap _,
   primewisePadicKernelExponents_realizationMap _⟩

end DirectImportsTests

#print axioms DirectImportsTests.zeroOnePowerImages
#print axioms DirectImportsTests.positivePowerQuotient
#print axioms DirectImportsTests.cyclicTwelvePositivePower
#print axioms DirectImportsTests.mixedProfile
#print axioms DirectImportsTests.actualMixedKernel
#print axioms DirectImportsTests.zeroTopExtracted
