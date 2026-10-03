/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups

/-!
# Public-root consumers

Use only the library's public root to combine realization, arbitrary-target
homomorphisms, and positive power-image results. The target of the homomorphism
need not be procyclic; power-image indices are asserted to divide the exponent.
-/

@[expose] public section

open ProfiniteGrp

universe u v

namespace PublicRootTests

/-- The prescribed-image criterion makes no procyclicity assumption on the target. -/
theorem arbitraryTargetCriterion (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) (h : H) :
    (∃! f : G →ₜ* H, f g = h) ↔
      ∀ p, primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator H h) p ≤
        hG.exponents p :=
  existsUnique_continuousHom_apply_generator_iff hG g hg h

/-- A positive power image is open and has index dividing, not necessarily equal to, `n`. -/
theorem positivePowerIndexDivides (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (n : ℕ) (hn : 0 < n) :
    IsOpen ((powerImage G hG n : Subgroup G) : Set G) ∧
      (powerImage G hG n : Subgroup G).index ∣ n :=
  ⟨powerImage_isOpen G hG n hn, powerImage_index_dvd G hG n hn⟩

/-- A root-import consumer obtains the fourth-power index divisibility for a
finite cyclic group. The exact smaller index is tested in `ProfiniteGroupsTests.ProcyclicPower`. -/
theorem cyclicTwoFourthIndexDivides :
    (powerImage (finiteCyclic 2) (finiteCyclic_isProcyclic 2) 4 :
      Subgroup (finiteCyclic 2)).index ∣ 4 :=
  (positivePowerIndexDivides _ _ 4 (by decide)).2

/-- The square subgroup of a finite cyclic group has a generator in its inherited topology. -/
theorem cyclicFourSquareSubgroupGenerator :
    ∃ g : ofClosedSubgroup (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2),
      (Subgroup.zpowers g).topologicalClosure = ⊤ :=
  (finiteCyclic_isProcyclic 4).exists_closedSubgroup_generator _

/-- Zero, positive finite and infinite exponents occur in one model. -/
def mixedProfile (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then 0 else if p.1 = 3 then 2 else ⊤

/-- Extracting the kernel profile recovers the original mixed family. -/
theorem mixedProfileExtracted :
    primewisePadicKernelExponents
      (primewisePadicRealizationMap.{u} mixedProfile) = mixedProfile :=
  primewisePadicKernelExponents_realizationMap mixedProfile

/-- The model realizes the three distinct exponent regimes at concrete primes. -/
theorem mixedProfileCoordinates :
    primewisePadicKernelExponents
      (primewisePadicRealizationMap.{1} mixedProfile) (⟨2, by decide⟩) = 0 ∧
    primewisePadicKernelExponents
      (primewisePadicRealizationMap.{1} mixedProfile) (⟨3, by decide⟩) = 2 ∧
    primewisePadicKernelExponents
      (primewisePadicRealizationMap.{1} mixedProfile) (⟨5, by decide⟩) = ⊤ := by
  have extraction : primewisePadicKernelExponents
      (primewisePadicRealizationMap.{1} mixedProfile) = mixedProfile :=
    primewisePadicKernelExponents_realizationMap mixedProfile
  rw [extraction]
  exact ⟨rfl, rfl, rfl⟩

/-- Uniform zero and top profiles are recovered, without identifying source integers. -/
theorem zeroAndTopProfiles :
    primewisePadicKernelExponents
      (primewisePadicRealizationMap.{1} (fun _ => (0 : ℕ∞))) =
        (fun _ => (0 : ℕ∞)) ∧
    primewisePadicKernelExponents
      (primewisePadicRealizationMap.{1} (fun _ => (⊤ : ℕ∞))) =
        (fun _ => (⊤ : ℕ∞)) :=
  ⟨primewisePadicKernelExponents_realizationMap _,
   primewisePadicKernelExponents_realizationMap _⟩

/-- The completion-map integer computation still follows from plain `simp`. -/
theorem completionIntegerSimp (G : ProfiniteGrp.{u}) (g : G) (n : ℤ) :
    integerCompletionMap G g
      (ProfiniteCompletion.etaFn
        (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
        (ULift.up (Multiplicative.ofAdd n))) = g ^ n := by
  simp

/-- The primewise equivalence's integer computation needs no special simp rule. -/
theorem completionEquivIntegerSimp (n : ℤ) :
    integerCompletionEquivPrimewisePadic.{u}
      (ProfiniteCompletion.etaFn
        (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
        (ULift.up (Multiplicative.ofAdd n))) = primewisePadicDiagonal n := by
  simp

/-- Cross-universe integer casts use the general ring-hom simp rule. -/
theorem universeIntegerSimp (n : ℤ) :
    primewisePadicRingChangeUniverse.{u,v} (n : primewisePadicRing.{u}) =
      (n : primewisePadicRing.{v}) := by
  simp

/-- Plain `simp` retains both zero- and one-power computations. -/
theorem zeroOnePowerSimp (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (x : G) :
    powerHom G hG 0 x = 1 ∧ powerHom G hG 1 x = x := by
  simp

/-- The original power-coordinate proposition is still solved by plain `simp`. -/
theorem powerCoordinatesSimp
    (G : ProfiniteGrp.{u}) (g : G) (hg : IsTopologicalGenerator G g)
    (n : ℤ) (p : Nat.Primes) :
    ((procyclicContinuousMulEquivModel G g hg (g ^ n)).toAdd) p =
    liftedPadicQuotientContinuousAddEquivFactor p
      (primewisePadicExponentsOfGenerator G g p)
      (Ideal.Quotient.mk
        (liftedPadicIdealOfExponent p (primewisePadicExponentsOfGenerator G g p))
        ((primewisePadicRingMultiplicativeEquiv.{u}.symm
          (primewisePadicDiagonal n)).toAdd p)) := by
  simp

/-- Finite-stage interpretation is valid for an arbitrary topology on the target. -/
theorem arbitraryTopologyStageInjective
    (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F]
    (U : FiniteQuotientHom.StageIndex G) :
    Function.Injective (FiniteQuotientHom.stageToContinuousHom G F U) :=
  FiniteQuotientHom.stageToContinuousHom_injective G F U

/-- The colimit's forward map needs no discreteness or topological-group law. -/
theorem arbitraryTopologyColimitInjective
    (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F] :
    Function.Injective (FiniteQuotientHom.HomColimit.toContinuousHom G F) :=
  FiniteQuotientHom.HomColimit.toContinuousHom_injective G F

/-- Removing the unused target assumption did not change the defining payload. -/
theorem stagePayloadUnchanged
    (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F]
    (U : FiniteQuotientHom.StageIndex G) (a : FiniteQuotientHom.HomStage G F U) :
    FiniteQuotientHom.stageToContinuousHom G F U a =
      ({ toMonoidHom := a.comp
           (QuotientGroup.mk' (OrderDual.ofDual U).toSubgroup)
         continuous_toFun :=
           (continuous_of_discreteTopology : Continuous a).comp
             continuous_quotient_mk' } : G →ₜ* F) := rfl

/-- In the discrete case the original two-sided hom equivalence still applies. -/
theorem discreteHomRoundTrip
    (G : ProfiniteGrp.{u}) (F : Type v) [Group F] [TopologicalSpace F]
    [DiscreteTopology F] (f : G →ₜ* F) :
    FiniteQuotientHom.HomColimit.toContinuousHom G F
      (FiniteQuotientHom.HomColimit.ofContinuousHom G F f) = f := by
  simp

/-- Equality-of-ideals transport works without compatibility of topology and ring laws. -/
theorem arbitraryTopologyIdealTransport
    {R : Type u} [CommRing R] [TopologicalSpace R]
    {I J : Ideal R} (h : I = J) (x : R) :
    Ideal.quotientContinuousAddEquivOfEq h (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J x := by
  simp

/-- Reflexive ideal transport retains its original definitional value. -/
theorem idealTransportPayloadUnchanged
    {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) :
    Ideal.quotientContinuousAddEquivOfEq (rfl : I = I) =
      ContinuousAddEquiv.refl (R ⧸ I) := rfl

end PublicRootTests

#print axioms PublicRootTests.arbitraryTargetCriterion
#print axioms PublicRootTests.positivePowerIndexDivides
#print axioms PublicRootTests.cyclicTwoFourthIndexDivides
#print axioms PublicRootTests.cyclicFourSquareSubgroupGenerator
#print axioms PublicRootTests.mixedProfile
#print axioms PublicRootTests.mixedProfileExtracted
#print axioms PublicRootTests.mixedProfileCoordinates
#print axioms PublicRootTests.zeroAndTopProfiles
#print axioms PublicRootTests.completionIntegerSimp
#print axioms PublicRootTests.completionEquivIntegerSimp
#print axioms PublicRootTests.universeIntegerSimp
#print axioms PublicRootTests.zeroOnePowerSimp
#print axioms PublicRootTests.powerCoordinatesSimp
#print axioms PublicRootTests.arbitraryTopologyStageInjective
#print axioms PublicRootTests.arbitraryTopologyColimitInjective
#print axioms PublicRootTests.stagePayloadUnchanged
#print axioms PublicRootTests.discreteHomRoundTrip
#print axioms PublicRootTests.arbitraryTopologyIdealTransport
#print axioms PublicRootTests.idealTransportPayloadUnchanged
