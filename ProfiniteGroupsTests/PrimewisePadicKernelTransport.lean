/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.PrimewisePadicKernelTransport

/-!
# Primewise kernel transport clients

Direct-import proof-use clients for the actual kernel universe transport.
Run in ordinary and `-T0` modes.
-/

@[expose] public section

open ProfiniteGrp

universe u v w

namespace PrimewisePadicKernelTransportTests

theorem commutingSquare (x : primewisePadicRing.{u}) :
    primewisePadicChangeUniverse.{u,v}
      (primewisePadicRingMultiplicativeEquiv.{u} (Multiplicative.ofAdd x)) =
    primewisePadicRingMultiplicativeEquiv.{v}
      (Multiplicative.ofAdd (primewisePadicRingChangeUniverse.{u,v} x)) :=
  primewisePadicChangeUniverse_ringMultiplicativeEquiv x

theorem arbitraryMapKernelMembership
    {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{v} →ₜ* Y) (x : primewisePadicRing.{u}) :
    x ∈ primewisePadicKernelIdeal
      (f.comp (primewisePadicChangeUniverse.{u,v} :
        primewisePadic.{u} →ₜ* primewisePadic.{v})) ↔
      f (primewisePadicRingMultiplicativeEquiv.{v}
        (Multiplicative.ofAdd (primewisePadicRingChangeUniverse.{u,v} x))) = 1 := by
  rw [primewisePadicKernelIdeal_comp_changeUniverse, Ideal.mem_comap,
    mem_primewisePadicKernelIdeal]

theorem arbitraryMapIdeal
    {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{v} →ₜ* Y) :
    primewisePadicKernelIdeal
      (f.comp (primewisePadicChangeUniverse.{u,v} :
        primewisePadic.{u} →ₜ* primewisePadic.{v})) =
      (primewisePadicKernelIdeal f).comap primewisePadicRingChangeUniverse.{u,v} :=
  primewisePadicKernelIdeal_comp_changeUniverse f

theorem arbitraryMapExponents
    {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{v} →ₜ* Y) :
    primewisePadicKernelExponents
      (f.comp (primewisePadicChangeUniverse.{u,v} :
        primewisePadic.{u} →ₜ* primewisePadic.{v})) =
      primewisePadicKernelExponents f :=
  primewisePadicKernelExponents_comp_changeUniverse f

theorem zeroToPositive
    {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{1} →ₜ* Y) :
    primewisePadicKernelExponents
      (f.comp (primewisePadicChangeUniverse.{0,1} :
        primewisePadic.{0} →ₜ* primewisePadic.{1})) =
      primewisePadicKernelExponents f :=
  primewisePadicKernelExponents_comp_changeUniverse f

theorem positiveToZero
    {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{0} →ₜ* Y) :
    primewisePadicKernelIdeal
      (f.comp (primewisePadicChangeUniverse.{1,0} :
        primewisePadic.{1} →ₜ* primewisePadic.{0})) =
      (primewisePadicKernelIdeal f).comap primewisePadicRingChangeUniverse.{1,0} :=
  primewisePadicKernelIdeal_comp_changeUniverse f

theorem identityInfinite (p : Nat.Primes) :
    primewisePadicKernelExponents
      ((ContinuousMonoidHom.id primewisePadic.{v}).comp
        (primewisePadicChangeUniverse.{u,v} :
          primewisePadic.{u} →ₜ* primewisePadic.{v})) p = ⊤ := by
  rw [primewisePadicKernelExponents_comp_changeUniverse]
  apply (primewisePadic_injective_iff_kernelExponents_eq_top _).mp _ p
  intro x y h
  exact h

theorem trivialZero (p : Nat.Primes) :
    primewisePadicKernelExponents
      ((1 : primewisePadic.{v} →ₜ* primewisePadic.{v}).comp
        (primewisePadicChangeUniverse.{u,v} :
          primewisePadic.{u} →ₜ* primewisePadic.{v})) p = 0 := by
  rw [primewisePadicKernelExponents_comp_changeUniverse]
  exact (primewisePadic_eq_one_iff_kernelExponents_eq_zero _).mp rfl p

theorem arbitraryElementComparison (G : ProfiniteGrp.{u}) (g : G) :
    primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G g) =
      primewisePadicExponentsOfGenerator G g :=
  primewisePadicKernelExponents_baseMapOfGenerator G g

theorem nongeneratorConstant (x : primewisePadic.{0}) :
    primewisePadicBaseMapOfGenerator (finiteCyclic 12) (1 : finiteCyclic 12) x = 1 := by
  have h := primewisePadicBaseMapOfGenerator_naturality
    (finiteCyclic 12) (finiteCyclic 12)
    (1 : finiteCyclic 12 →ₜ* finiteCyclic 12)
    (finiteCyclicGenerator 12)
  have hx := congrArg (fun f : primewisePadic.{0} →ₜ* finiteCyclic 12 ↦ f x) h
  simpa using hx.symm

theorem nongeneratorZero (p : Nat.Primes) :
    primewisePadicExponentsOfGenerator (finiteCyclic 12) (1 : finiteCyclic 12) p = 0 := by
  rw [← primewisePadicKernelExponents_baseMapOfGenerator]
  apply (primewisePadic_eq_one_iff_kernelExponents_eq_zero _).mp _ p
  ext x
  exact nongeneratorConstant x

theorem nongeneratorNotSurjective :
    ¬ Function.Surjective
      (primewisePadicBaseMapOfGenerator (finiteCyclic 12) (1 : finiteCyclic 12)) := by
  intro hs
  obtain ⟨x, hx⟩ := hs (finiteCyclicGenerator 12)
  have heq : (finiteCyclicGenerator 12 : finiteCyclic 12) = 1 :=
    hx.symm.trans (nongeneratorConstant x)
  exact (by decide : (1 : ZMod 12) ≠ 0) (congrArg Multiplicative.toAdd heq)

/-- The prime two, used for concrete transport checks. -/
def twoPrime : Nat.Primes := ⟨2, by decide⟩
/-- The prime three, used for concrete transport checks. -/
def threePrime : Nat.Primes := ⟨3, by decide⟩
/-- The prime five, used for concrete transport checks. -/
def fivePrime : Nat.Primes := ⟨5, by decide⟩

/-- The zero/finite/infinite profile for kernel universe transport. -/
noncomputable def mixedExponents (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then 0 else if p.1 = 3 then 2 else ⊤

/-- The realization map used to check the actual transported kernel. -/
noncomputable def mixedMap :
    primewisePadic.{1} →ₜ*
      Multiplicative (primewisePadicQuotientModel mixedExponents) := by
  let I := primewisePadicIdealOfExponents mixedExponents
  let quotientMap : primewisePadic.{1} →ₜ*
      Multiplicative (primewisePadicRing.{1} ⧸ I) :=
    ContinuousMonoidHom.mk
      (((Ideal.Quotient.mk I).toAddMonoidHom.toMultiplicative).comp
        primewisePadicRingMultiplicativeEquiv.{1}.symm.toMulEquiv.toMonoidHom)
      (by
        change Continuous (Multiplicative.ofAdd ∘ Ideal.Quotient.mk I ∘
          Multiplicative.toAdd ∘ primewisePadicRingMultiplicativeEquiv.{1}.symm)
        exact continuous_ofAdd.comp
          ((QuotientRing.isOpenQuotientMap_mk I).continuous.comp
            (continuous_toAdd.comp
              primewisePadicRingMultiplicativeEquiv.{1}.symm.continuous_toFun)))
  exact (ContinuousMonoidHom.toContinuousMonoidHom
    (primewisePadicQuotientContinuousAddEquivModel mixedExponents).toMultiplicative).comp
      quotientMap

theorem mixedMap_mk (x : primewisePadicRing.{1}) :
    mixedMap (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) =
      Multiplicative.ofAdd
        (primewisePadicQuotientContinuousAddEquivModel mixedExponents
          (Ideal.Quotient.mk (primewisePadicIdealOfExponents mixedExponents) x)) := by
  rfl

theorem mixedMap_kernelIdeal :
    primewisePadicKernelIdeal mixedMap =
      primewisePadicIdealOfExponents mixedExponents := by
  ext x
  rw [mem_primewisePadicKernelIdeal, mixedMap_mk]
  constructor
  · intro hx
    have hx0 : primewisePadicQuotientContinuousAddEquivModel mixedExponents
        (Ideal.Quotient.mk (primewisePadicIdealOfExponents mixedExponents) x) = 0 :=
      congrArg Multiplicative.toAdd hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((primewisePadicQuotientContinuousAddEquivModel mixedExponents).injective
        (by simpa using hx0))
  · intro hx
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    rfl

theorem mixedKernelIdeal :
    primewisePadicKernelIdeal
      (mixedMap.comp (primewisePadicChangeUniverse.{0,1} :
        primewisePadic.{0} →ₜ* primewisePadic.{1})) =
      primewisePadicIdealOfExponents.{0} mixedExponents := by
  rw [primewisePadicKernelIdeal_comp_changeUniverse, mixedMap_kernelIdeal]
  exact primewisePadicIdealOfExponents_comap_changeUniverse mixedExponents

theorem mixedExponent (p : Nat.Primes) :
    primewisePadicKernelExponents
      (mixedMap.comp (primewisePadicChangeUniverse.{0,1} :
        primewisePadic.{0} →ₜ* primewisePadic.{1})) p = mixedExponents p := by
  rw [primewisePadicKernelExponents_comp_changeUniverse]
  change primewisePadicIdealExponents (primewisePadicKernelIdeal mixedMap) p = _
  rw [mixedMap_kernelIdeal, primewisePadicIdealExponents_idealOfExponents]

theorem mixedZero :
    primewisePadicKernelExponents
      (mixedMap.comp (primewisePadicChangeUniverse.{0,1} :
        primewisePadic.{0} →ₜ* primewisePadic.{1})) twoPrime = 0 := by
  rw [mixedExponent]
  simp [mixedExponents, twoPrime]

theorem mixedFinite :
    primewisePadicKernelExponents
      (mixedMap.comp (primewisePadicChangeUniverse.{0,1} :
        primewisePadic.{0} →ₜ* primewisePadic.{1})) threePrime = 2 := by
  rw [mixedExponent]
  simp [mixedExponents, threePrime]

theorem mixedInfinite :
    primewisePadicKernelExponents
      (mixedMap.comp (primewisePadicChangeUniverse.{0,1} :
        primewisePadic.{0} →ₜ* primewisePadic.{1})) fivePrime = ⊤ := by
  rw [mixedExponent]
  simp [mixedExponents, fivePrime]

theorem mixedNotTrivial :
    mixedMap.comp (primewisePadicChangeUniverse.{0,1} :
      primewisePadic.{0} →ₜ* primewisePadic.{1}) ≠ 1 := by
  intro heq
  have h := (primewisePadic_eq_one_iff_kernelExponents_eq_zero _).mp heq threePrime
  rw [mixedFinite] at h
  exact (by decide : (2 : ℕ∞) ≠ 0) h

theorem mixedNotInjective :
    ¬ Function.Injective
      (mixedMap.comp (primewisePadicChangeUniverse.{0,1} :
        primewisePadic.{0} →ₜ* primewisePadic.{1})) := by
  intro hinj
  have h := (primewisePadic_injective_iff_kernelExponents_eq_top _).mp hinj twoPrime
  rw [mixedZero] at h
  exact (by decide : (0 : ℕ∞) ≠ ⊤) h

end PrimewisePadicKernelTransportTests
