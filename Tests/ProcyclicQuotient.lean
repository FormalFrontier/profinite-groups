/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups
public import Tests.PrimewisePadicQuotients

/-!
# Primewise quotient client checks

Downstream checks for the primewise first-isomorphism bridge and the
generator-dependent quotient model. Run with and without `-T0`.
-/

@[expose] public section

open ProfiniteGrp Function

universe u v

section Generic

variable {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
variable (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f)

noncomputable example :
    Multiplicative (primewisePadicRing.{u} ⧸ primewisePadicKernelIdeal f) ≃ₜ* Y :=
  primewisePadicKernelIdealContinuousMulEquiv f hf

example (x : primewisePadicRing.{u}) :
    primewisePadicKernelIdealContinuousMulEquiv f hf
      (Multiplicative.ofAdd (Ideal.Quotient.mk (primewisePadicKernelIdeal f) x)) =
      f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) := by
  simp

example (x : primewisePadicRing.{u}) :
    (primewisePadicKernelIdealContinuousMulEquiv f hf).symm
      (f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x))) =
      Multiplicative.ofAdd (Ideal.Quotient.mk (primewisePadicKernelIdeal f) x) := by
  simp

example (y : Y) :
    primewisePadicKernelIdealContinuousMulEquiv f hf
      ((primewisePadicKernelIdealContinuousMulEquiv f hf).symm y) = y := by simp

example (x : primewisePadicRing.{u}) (p : Nat.Primes) :
    ((primewisePadicContinuousMulEquivModel f hf)
      (f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)))).toAdd p =
      liftedPadicQuotientContinuousAddEquivFactor p
        (primewisePadicKernelExponents f p)
        (Ideal.Quotient.mk
          (liftedPadicIdealOfExponent p (primewisePadicKernelExponents f p))
          (x p)) := by
  simp

end Generic

section Generators

variable (G : ProfiniteGrp.{u}) (g : G) (hg : IsTopologicalGenerator G g)

example (n : ℤ) : primewisePadicMapOfGenerator G g (primewisePadicDiagonal n) =
    g ^ n := by simp

example : Surjective (primewisePadicMapOfGenerator G g) :=
  primewisePadicMapOfGenerator_surjective G g hg

noncomputable example :
    G ≃ₜ* Multiplicative (primewisePadicQuotientModel
      (primewisePadicExponentsOfGenerator G g)) :=
  procyclicContinuousMulEquivModel G g hg

example (y : G) :
    (procyclicContinuousMulEquivModel G g hg).symm
      (procyclicContinuousMulEquivModel G g hg y) = y := by simp

example (n : ℤ) (p : Nat.Primes) :
    ((procyclicContinuousMulEquivModel G g hg (g ^ n)).toAdd) p =
      liftedPadicQuotientContinuousAddEquivFactor p
        (primewisePadicExponentsOfGenerator G g p)
        (Ideal.Quotient.mk
          (liftedPadicIdealOfExponent p (primewisePadicExponentsOfGenerator G g p))
          ((primewisePadicRingMultiplicativeEquiv.{u}.symm
            (primewisePadicDiagonal n)).toAdd p)) := by
  exact procyclicContinuousMulEquivModel_zpow_apply G g hg n p

end Generators

private theorem trivialGenerator : IsTopologicalGenerator
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit)) PUnit.unit := by
  change DenseRange (fun n : ℤ ↦ (PUnit.unit : PUnit) ^ n)
  apply Function.Surjective.denseRange
  intro x
  exact ⟨0, by cases x; rfl⟩

noncomputable example :
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit)) ≃ₜ*
      Multiplicative (primewisePadicQuotientModel
        (primewisePadicExponentsOfGenerator
          (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit)) PUnit.unit)) :=
  procyclicContinuousMulEquivModel _ _ trivialGenerator

example (n : ℕ) [NeZero n] :
    IsTopologicalGenerator (finiteCyclic n) (finiteCyclicGenerator n) :=
  finiteCyclicGenerator_isTopologicalGenerator n

noncomputable example :
    finiteCyclic 1 ≃ₜ* Multiplicative (primewisePadicQuotientModel
      (primewisePadicExponentsOfGenerator (finiteCyclic 1)
        (finiteCyclicGenerator 1))) :=
  procyclicContinuousMulEquivModel _ _
    (finiteCyclicGenerator_isTopologicalGenerator 1)

noncomputable example :
    finiteCyclic 12 ≃ₜ* Multiplicative (primewisePadicQuotientModel
      (primewisePadicExponentsOfGenerator (finiteCyclic 12)
        (finiteCyclicGenerator 12))) :=
  procyclicContinuousMulEquivModel _ _
    (finiteCyclicGenerator_isTopologicalGenerator 12)

noncomputable example :
    primewisePadic.{1} ≃ₜ* Multiplicative (primewisePadicQuotientModel
      (primewisePadicExponentsOfGenerator primewisePadic.{1}
        primewisePadicGenerator)) :=
  procyclicContinuousMulEquivModel _ _
    primewisePadicGenerator_isTopologicalGenerator

example (p : Nat.Primes) :
    primewisePadicKernelExponents
      (ContinuousMonoidHom.id primewisePadic.{1}) p = ⊤ :=
  (primewisePadic_injective_iff_kernelExponents_eq_top _).mp
    (fun _ _ h ↦ h) p

noncomputable example :
    Multiplicative (primewisePadicRing.{1} ⧸
      primewisePadicKernelIdeal (ContinuousMonoidHom.id primewisePadic.{1})) ≃ₜ*
      primewisePadic.{1} :=
  primewisePadicKernelIdealContinuousMulEquiv
    (ContinuousMonoidHom.id primewisePadic.{1}) (fun x ↦ ⟨x, rfl⟩)

example (x : primewisePadicRing.{1}) :
    primewisePadicKernelIdealContinuousMulEquiv
      (ContinuousMonoidHom.id primewisePadic.{1}) (fun y ↦ ⟨y, rfl⟩)
        (Multiplicative.ofAdd
          (Ideal.Quotient.mk
            (primewisePadicKernelIdeal (ContinuousMonoidHom.id primewisePadic.{1})) x)) =
      primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x) := by
  exact primewisePadicKernelIdealContinuousMulEquiv_mk
    (ContinuousMonoidHom.id primewisePadic.{1}) (fun y ↦ ⟨y, rfl⟩) x

/-- The mixed quotient map used by both quotient and generator-independence clients. -/
noncomputable def mixedPrimewiseMap :
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

/-- The mixed quotient has zero, positive finite, and top exponents. -/
@[simp]
theorem mixedPrimewiseMap_mk (x : primewisePadicRing.{1}) :
    mixedPrimewiseMap
      (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) =
      Multiplicative.ofAdd
        (primewisePadicQuotientContinuousAddEquivModel mixedExponents
          (Ideal.Quotient.mk (primewisePadicIdealOfExponents mixedExponents) x)) := by
  rfl

theorem mixedPrimewiseMap_surjective : Surjective mixedPrimewiseMap := by
  unfold mixedPrimewiseMap
  apply (ContinuousAddEquiv.toMultiplicative
    (primewisePadicQuotientContinuousAddEquivModel mixedExponents)).surjective.comp
  apply Ideal.Quotient.mk_surjective.comp
  exact primewisePadicRingMultiplicativeEquiv.{1}.symm.surjective

theorem mixedPrimewiseMap_kernelIdeal :
    primewisePadicKernelIdeal mixedPrimewiseMap =
      primewisePadicIdealOfExponents mixedExponents := by
  ext x
  rw [mem_primewisePadicKernelIdeal, mixedPrimewiseMap_mk]
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

example (p : Nat.Primes) :
    primewisePadicKernelExponents mixedPrimewiseMap p = mixedExponents p := by
  have heq := primewisePadicIdealOfExponents_injective
    ((primewisePadicKernelIdeal_eq_idealOfExponents mixedPrimewiseMap).symm.trans
      mixedPrimewiseMap_kernelIdeal)
  exact congrFun heq p

example : ¬ Injective mixedPrimewiseMap := by
  let spike : primewisePadicRing.{1} := fun p ↦ if p.1 = 2 then 1 else 0
  have hspike : spike ≠ 0 := by
    intro h
    have h2 := congrFun h (⟨2, by decide⟩ : Nat.Primes)
    change (1 : ULift.{1} ℤ_[2]) = 0 at h2
    exact one_ne_zero h2
  have hmem : spike ∈ primewisePadicIdealOfExponents mixedExponents := by
    rw [mem_primewisePadicIdealOfExponents]
    intro p
    by_cases h2 : p.1 = 2
    · simp [spike, mixedExponents, h2, liftedPadicIdealOfExponent_zero]
    · simp [spike, h2]
  have himage : mixedPrimewiseMap
      (primewisePadicRingMultiplicativeEquiv
        (Multiplicative.ofAdd spike)) = 1 := by
    rw [mixedPrimewiseMap_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
    rfl
  have hnontrivial : primewisePadicRingMultiplicativeEquiv
      (Multiplicative.ofAdd spike) ≠ 1 := by
    intro heq
    apply hspike
    have hh := congrArg
      (fun y ↦ (primewisePadicRingMultiplicativeEquiv.{1}.symm y).toAdd) heq
    simpa using hh
  intro hinj
  apply hnontrivial
  apply hinj
  simpa using himage

noncomputable example :
    Multiplicative (primewisePadicRing.{1} ⧸
      primewisePadicKernelIdeal mixedPrimewiseMap) ≃ₜ*
      Multiplicative (primewisePadicQuotientModel mixedExponents) :=
  primewisePadicKernelIdealContinuousMulEquiv mixedPrimewiseMap
    mixedPrimewiseMap_surjective

#print axioms mixedExponents
#print axioms mixedPrimewiseMap
#print axioms mixedPrimewiseMap_mk
#print axioms mixedPrimewiseMap_surjective
#print axioms mixedPrimewiseMap_kernelIdeal
