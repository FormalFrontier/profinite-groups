/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups

/-!
# Torsion-free quotient clients

Downstream checks for zero, finite, infinite, and mixed quotient exponents,
independent source and target universes, and supplied generators. Run in
ordinary and `-T0` modes.
-/

@[expose] public section

open ProfiniteGrp

universe u v

private def twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩

example (p : Nat.Primes) : IsAddTorsionFree (padicQuotientFactor.{u} p 0) :=
  (padicQuotientFactor_isAddTorsionFree_iff p 0).mpr (Or.inl rfl)

example (p : Nat.Primes) : IsAddTorsionFree (padicQuotientFactor.{1} p ⊤) :=
  (padicQuotientFactor_isAddTorsionFree_iff p ⊤).mpr (Or.inr rfl)

example (p : Nat.Primes) : ¬ IsAddTorsionFree
    (padicQuotientFactor.{0} p (2 : ℕ∞)) := by
  intro h
  have he := (padicQuotientFactor_isAddTorsionFree_iff p 2).mp h
  norm_num at he

example : IsAddTorsionFree (primewisePadicQuotientModel.{0} fun _ ↦ 0) :=
  (primewisePadicQuotientModel_isAddTorsionFree_iff _).mpr (fun _ ↦ Or.inl rfl)

example : IsAddTorsionFree (primewisePadicQuotientModel.{1} fun _ ↦ ⊤) :=
  (primewisePadicQuotientModel_isAddTorsionFree_iff _).mpr (fun _ ↦ Or.inr rfl)

private def zeroOrTopExponents (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then 0 else ⊤

example : IsAddTorsionFree (primewisePadicQuotientModel.{1} zeroOrTopExponents) :=
  (primewisePadicQuotientModel_isAddTorsionFree_iff _).mpr (by
    intro p
    by_cases hp : p.1 = 2
    · exact Or.inl (by simp [zeroOrTopExponents, hp])
    · exact Or.inr (by simp [zeroOrTopExponents, hp]))

private def finiteOrTopExponents (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then 3 else ⊤

example : ¬ IsAddTorsionFree (primewisePadicQuotientModel.{1} finiteOrTopExponents) := by
  intro h
  have htwo := (primewisePadicQuotientModel_isAddTorsionFree_iff
    finiteOrTopExponents).mp h twoPrime
  norm_num [finiteOrTopExponents, twoPrime] at htwo

section SurjectiveMap

variable {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
variable (f : primewisePadic.{u} →ₜ* Y) (hf : Function.Surjective f)

example (h : IsMulTorsionFree Y) (p : Nat.Primes) :
    primewisePadicKernelExponents f p = 0 ∨
      primewisePadicKernelExponents f p = ⊤ :=
  (primewisePadicSurjective_isMulTorsionFree_iff f hf).mp h p

example (h : ∀ p, primewisePadicKernelExponents f p = 0 ∨
      primewisePadicKernelExponents f p = ⊤) : IsMulTorsionFree Y :=
  (primewisePadicSurjective_isMulTorsionFree_iff f hf).mpr h

end SurjectiveMap

example : IsMulTorsionFree primewisePadic.{1} := by
  apply (primewisePadicSurjective_isMulTorsionFree_iff
    (ContinuousMonoidHom.id primewisePadic.{1}) (fun x ↦ ⟨x, rfl⟩)).mpr
  intro p
  right
  exact (primewisePadic_injective_iff_kernelExponents_eq_top _).mp
    (fun _ _ h ↦ h) p

example (G : ProfiniteGrp.{u}) (g : G) (hg : IsTopologicalGenerator G g)
    (h : IsMulTorsionFree G) (p : Nat.Primes) :
    primewisePadicExponentsOfGenerator G g p = 0 ∨
      primewisePadicExponentsOfGenerator G g p = ⊤ :=
  (isMulTorsionFree_iff_exponentsOfGenerator G g hg).mp h p

example (G : ProfiniteGrp.{1}) (g : G) (hg : IsTopologicalGenerator G g)
    (h : ∀ p, primewisePadicExponentsOfGenerator G g p = 0 ∨
      primewisePadicExponentsOfGenerator G g p = ⊤) : IsMulTorsionFree G :=
  (isMulTorsionFree_iff_exponentsOfGenerator G g hg).mpr h

example : ∀ p, primewisePadicExponentsOfGenerator (finiteCyclic 1)
      (finiteCyclicGenerator 1) p = 0 ∨
      primewisePadicExponentsOfGenerator (finiteCyclic 1)
        (finiteCyclicGenerator 1) p = ⊤ := by
  apply (isMulTorsionFree_iff_exponentsOfGenerator (finiteCyclic 1)
    (finiteCyclicGenerator 1) (finiteCyclicGenerator_isTopologicalGenerator 1)).mp
  have htrivial : Subsingleton (finiteCyclic 1) := by
    change Subsingleton (Multiplicative (ZMod 1))
    infer_instance
  exact Subsingleton.to_isMulTorsionFree

example : ¬ ∀ p, primewisePadicExponentsOfGenerator (finiteCyclic 12)
      (finiteCyclicGenerator 12) p = 0 ∨
      primewisePadicExponentsOfGenerator (finiteCyclic 12)
        (finiteCyclicGenerator 12) p = ⊤ := by
  intro he
  have hfree := (isMulTorsionFree_iff_exponentsOfGenerator (finiteCyclic 12)
    (finiteCyclicGenerator 12) (finiteCyclicGenerator_isTopologicalGenerator 12)).mpr he
  have hresidue : IsMulTorsionFree (Multiplicative (ZMod 12)) := by
    change IsMulTorsionFree (finiteCyclic 12)
    exact hfree
  have hone : (Multiplicative.ofAdd (1 : ZMod 12)) ≠ (1 : Multiplicative (ZMod 12)) := by
    decide
  have hpow : (Multiplicative.ofAdd (1 : ZMod 12)) ^ 12 =
      (1 : Multiplicative (ZMod 12)) := by
    change (12 • (1 : ZMod 12)) = 0
    simpa only [nsmul_eq_mul, mul_one] using (CharP.cast_eq_zero (ZMod 12) 12)
  exact hone ((pow_eq_one_iff_left (n := 12) (by decide)).mp hpow)
