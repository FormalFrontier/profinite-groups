/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups
public import ProfiniteGroupsTests.ProcyclicQuotient

/-!
# Generator-independence client checks

Downstream checks for generator-independent kernels and exponents. Run with
and without `-T0`; the imported mixed quotient is constructed in the existing
quotient client.
-/

@[expose] public section

open ProfiniteGrp Function

universe u v

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

section Generic

variable {R : Type u} {A : Type v}
variable [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
variable [AddGroup A] [TopologicalSpace A] [T2Space A]

example (dense : DenseRange (fun n : ℤ => (n : R)))
    (f h : R →+ A) (cf : Continuous f) (ch : Continuous h)
    (sf : Surjective f) (sh : Surjective h) : f.ker = h.ker :=
  AddMonoidHom.ker_eq_of_surjective_dense_intCast dense f h cf ch sf sh

end Generic

private def negIntegers : ℤ →+ ℤ where
  toFun n := -n
  map_zero' := by simp
  map_add' x y := by simp [add_comm]

example : (AddMonoidHom.id ℤ).ker = negIntegers.ker := by
  apply AddMonoidHom.ker_eq_of_surjective_dense_intCast
    (Function.Surjective.denseRange (fun n : ℤ => ⟨n, rfl⟩))
  · exact continuous_of_discreteTopology
  · exact continuous_of_discreteTopology
  · exact fun n => ⟨n, rfl⟩
  · exact fun n => ⟨-n, by simp [negIntegers]⟩

private def fiveZMod : ZMod 12 →+ ZMod 12 where
  toFun x := 5 * x
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

private theorem fiveZMod_surjective : Surjective fiveZMod := by
  intro x
  refine ⟨5 * x, ?_⟩
  change (5 : ZMod 12) * (5 * x) = x
  rw [← mul_assoc, show (5 : ZMod 12) * 5 = 1 by decide, one_mul]

example : (AddMonoidHom.id (ZMod 12)).ker = fiveZMod.ker := by
  apply AddMonoidHom.ker_eq_of_surjective_dense_intCast
    (Function.Surjective.denseRange ZMod.intCast_surjective)
  · exact continuous_of_discreteTopology
  · exact continuous_of_discreteTopology
  · exact fun x => ⟨x, rfl⟩
  · exact fiveZMod_surjective

example : (AddMonoidHom.id (ZMod 12)) ≠ fiveZMod := by
  intro equal_maps
  have at_one := congrArg (fun f : ZMod 12 →+ ZMod 12 => f 1) equal_maps
  change (1 : ZMod 12) = 5 at at_one
  exact (by decide : (1 : ZMod 12) ≠ 5) at_one

section Quotients

variable {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
variable (f h : primewisePadic.{u} →ₜ* Y)
variable (sf : Surjective f) (sh : Surjective h)

example : primewisePadicKernelIdeal f = primewisePadicKernelIdeal h :=
  primewisePadicKernelIdeal_eq_of_surjective f h sf sh

end Quotients

section Generators

variable (G : ProfiniteGrp.{u}) (g h : G)
variable (hg : IsTopologicalGenerator G g)
variable (hh : IsTopologicalGenerator G h)

example : primewisePadicKernelIdeal (primewisePadicMapOfGenerator G g) =
    primewisePadicKernelIdeal (primewisePadicMapOfGenerator G h) :=
  primewisePadicKernelIdeal_mapOfGenerator_eq G g h hg hh

example : primewisePadicExponentsOfGenerator G g =
    primewisePadicExponentsOfGenerator G h :=
  primewisePadicExponentsOfGenerator_eq G g h hg hh

end Generators

private theorem trivialGenerator : IsTopologicalGenerator
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit.{1})) PUnit.unit := by
  change DenseRange (fun n : ℤ => (PUnit.unit : PUnit.{1}) ^ n)
  apply Function.Surjective.denseRange
  intro x
  exact ⟨0, by cases x; rfl⟩

example : Surjective (primewisePadicMapOfGenerator
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit.{1})) PUnit.unit) :=
  primewisePadicMapOfGenerator_surjective _ _ trivialGenerator

example : primewisePadicExponentsOfGenerator
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit.{1})) PUnit.unit =
    primewisePadicExponentsOfGenerator
      (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit.{1})) PUnit.unit := by
  exact primewisePadicExponentsOfGenerator_eq
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit.{1}))
    (PUnit.unit : PUnit.{1}) (PUnit.unit : PUnit.{1})
    trivialGenerator trivialGenerator

private theorem fiveGenerator : IsTopologicalGenerator
    (finiteCyclic 12) (Multiplicative.ofAdd (5 : ZMod 12)) := by
  apply Function.Surjective.denseRange
  intro x
  change Multiplicative (ZMod 12) at x
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨5 * k, Multiplicative.toAdd.injective ?_⟩
  change (5 * k) • (5 : ZMod 12) = x.toAdd
  have h55 : (5 : ℤ) • (5 : ZMod 12) = 1 := by decide
  calc
    (5 * k) • (5 : ZMod 12) = k • ((5 : ℤ) • (5 : ZMod 12)) := by
      rw [mul_comm 5 k, mul_zsmul]
    _ = k • (1 : ZMod 12) := congrArg (fun z : ZMod 12 => k • z) h55
    _ = x.toAdd := by simpa only [zsmul_one] using hk

example : primewisePadicKernelIdeal
    (primewisePadicMapOfGenerator (finiteCyclic 12) (finiteCyclicGenerator 12)) =
    primewisePadicKernelIdeal
      (primewisePadicMapOfGenerator (finiteCyclic 12)
        (Multiplicative.ofAdd (5 : ZMod 12))) :=
  primewisePadicKernelIdeal_mapOfGenerator_eq _ _ _
    (finiteCyclicGenerator_isTopologicalGenerator 12) fiveGenerator

example : primewisePadicExponentsOfGenerator
    (finiteCyclic 12) (finiteCyclicGenerator 12) =
    primewisePadicExponentsOfGenerator
      (finiteCyclic 12) (Multiplicative.ofAdd (5 : ZMod 12)) :=
  primewisePadicExponentsOfGenerator_eq _ _ _
    (finiteCyclicGenerator_isTopologicalGenerator 12) fiveGenerator

example : primewisePadicMapOfGenerator (finiteCyclic 12)
    (finiteCyclicGenerator 12) ≠
    primewisePadicMapOfGenerator (finiteCyclic 12)
      (Multiplicative.ofAdd (5 : ZMod 12)) := by
  intro equal_maps
  have at_diagonal := congrArg
    (fun f : primewisePadic →ₜ* finiteCyclic 12 => f (primewisePadicDiagonal 1))
    equal_maps
  rw [primewisePadicMapOfGenerator_diagonal (finiteCyclic 12)
    (Multiplicative.ofAdd (5 : ZMod 12)) 1,
    primewisePadicMapOfGenerator_diagonal (finiteCyclic 12)
      (finiteCyclicGenerator 12) 1] at at_diagonal
  simp only [zpow_one] at at_diagonal
  have at_one := congrArg Multiplicative.toAdd at_diagonal
  change (1 : ZMod 12) = 5 at at_one
  exact (by decide : (1 : ZMod 12) ≠ 5) at_one

private theorem inverseGenerator {G : ProfiniteGrp.{u}} {g : G}
    (hg : IsTopologicalGenerator G g) : IsTopologicalGenerator G g⁻¹ := by
  have expression : (fun n : ℤ => g⁻¹ ^ n) =
      (fun n : ℤ => g ^ n) ∘ (fun n : ℤ => -n) := by
    funext n
    simp [zpow_neg]
  change DenseRange (fun n : ℤ => g⁻¹ ^ n)
  rw [expression]
  exact hg.comp (Function.Surjective.denseRange
    (fun n : ℤ => ⟨-n, by simp⟩)) continuous_of_discreteTopology

example : primewisePadicExponentsOfGenerator primewisePadic.{1}
    primewisePadicGenerator =
    primewisePadicExponentsOfGenerator primewisePadic.{1}
      primewisePadicGenerator⁻¹ :=
  primewisePadicExponentsOfGenerator_eq _ _ _
    primewisePadicGenerator_isTopologicalGenerator
    (inverseGenerator primewisePadicGenerator_isTopologicalGenerator)

example : primewisePadicKernelIdeal
    (primewisePadicMapOfGenerator primewisePadic.{1} primewisePadicGenerator) =
    primewisePadicKernelIdeal
      (primewisePadicMapOfGenerator primewisePadic.{1} primewisePadicGenerator⁻¹) :=
  primewisePadicKernelIdeal_mapOfGenerator_eq _ _ _
    primewisePadicGenerator_isTopologicalGenerator
    (inverseGenerator primewisePadicGenerator_isTopologicalGenerator)

private noncomputable def primewiseInversion :
    primewisePadic.{1} →ₜ* primewisePadic.{1} where
  toMonoidHom := {
    toFun := fun x => x⁻¹
    map_one' := by simp
    map_mul' := by
      intro x y
      change (fun p : Nat.Primes => (x p * y p)⁻¹) =
        (fun p : Nat.Primes => (x p)⁻¹ * (y p)⁻¹)
      funext p
      rw [mul_inv_rev]
      exact mul_comm
        ((y p)⁻¹ : Multiplicative (ULift.{1} ℤ_[p.1]))
        ((x p)⁻¹ : Multiplicative (ULift.{1} ℤ_[p.1]))
  }
  continuous_toFun := continuous_inv

example : primewisePadicKernelIdeal mixedPrimewiseMap =
    primewisePadicKernelIdeal
      (mixedPrimewiseMap.comp primewiseInversion) :=
  primewisePadicKernelIdeal_eq_of_surjective _ _ mixedPrimewiseMap_surjective
    (mixedPrimewiseMap_surjective.comp
      (fun x => ⟨x⁻¹, by change (x⁻¹)⁻¹ = x; simp⟩))

example : primewisePadicKernelExponents mixedPrimewiseMap =
    primewisePadicKernelExponents (mixedPrimewiseMap.comp primewiseInversion) := by
  exact congrArg primewisePadicIdealExponents
    (primewisePadicKernelIdeal_eq_of_surjective _ _ mixedPrimewiseMap_surjective
      (mixedPrimewiseMap_surjective.comp
        (fun x => ⟨x⁻¹, by change (x⁻¹)⁻¹ = x; simp⟩)))

#print axioms AddMonoidHom.ker_eq_of_surjective_dense_intCast
#print axioms ProfiniteGrp.primewisePadicKernelIdeal_eq_of_surjective
#print axioms ProfiniteGrp.primewisePadicKernelIdeal_mapOfGenerator_eq
#print axioms ProfiniteGrp.primewisePadicExponentsOfGenerator_eq
#print axioms negIntegers
#print axioms fiveZMod
#print axioms fiveZMod_surjective
#print axioms trivialGenerator
#print axioms fiveGenerator
#print axioms inverseGenerator
#print axioms primewiseInversion
