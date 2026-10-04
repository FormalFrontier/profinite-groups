/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicQuotient
public import Mathlib.Algebra.Group.Pi.Torsion
public import Mathlib.Algebra.Ring.Torsion

/-!
# Torsion-free primewise p-adic quotient models

A primewise p-adic quotient model is torsion-free precisely when each coordinate
is either trivial (exponent zero) or an entire p-adic integer factor (exponent
infinity). The same criterion holds for a surjective continuous image of the
primewise p-adic group, and for a profinite group with a supplied topological
generator.

Positive finite exponents contribute nonzero torsion. The zero exponent has
a trivial coordinate, so it is consistent with torsion-freeness.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (torsion-free procyclic groups as products of p-adic integers).
- Mathlib, `Mathlib.Algebra.Group.Pi.Torsion` and `Mathlib.Algebra.Ring.Torsion` (torsion
  in p-adic products).
-/

@[expose] public section

universe u v

namespace ProfiniteGrp

open scoped IsDomain
local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The infinite-exponent factor is additively torsion-free. -/
private theorem padicQuotientFactorTop_isAddTorsionFree (p : Nat.Primes) :
    IsAddTorsionFree (padicQuotientFactorTop.{u} p) := by
  change IsAddTorsionFree (ULift.{u} ℤ_[p.1])
  have hpadic : IsAddTorsionFree ℤ_[p.1] := inferInstance
  let hom := (ULift.ringEquiv (R := ℤ_[p.1])).toAddMonoidHom
  exact (show Function.Injective hom from
    (ULift.ringEquiv (R := ℤ_[p.1])).injective).isAddTorsionFree hom

/-- The zero-exponent factor is trivial, hence additively torsion-free. -/
private theorem padicQuotientFactorNat_zero_isAddTorsionFree (p : Nat.Primes) :
    IsAddTorsionFree (padicQuotientFactorNat.{u} p 0) := by
  change IsAddTorsionFree (ULift.{u} (ZMod 1))
  infer_instance

/-- A positive finite exponent leaves a nonzero residue of finite additive order. -/
private theorem padicQuotientFactorNat_not_isAddTorsionFree
    (p : Nat.Primes) (n : ℕ) (hn : n ≠ 0) :
    ¬ IsAddTorsionFree (padicQuotientFactorNat.{u} p n) := by
  intro h
  have hfactor : IsAddTorsionFree (ULift.{u} (ZMod (p.1 ^ n))) := by
    change IsAddTorsionFree (padicQuotientFactorNat.{u} p n)
    exact h
  let hom := ((ULift.ringEquiv (R := ZMod (p.1 ^ n))).symm).toAddMonoidHom
  have hresidue : IsAddTorsionFree (ZMod (p.1 ^ n)) :=
    (show Function.Injective hom from
      (ULift.ringEquiv (R := ZMod (p.1 ^ n))).symm.injective).isAddTorsionFree hom
  have hpow : 1 < p.1 ^ n := one_lt_pow' p.2.one_lt hn
  have hnontrivial : Nontrivial (ZMod (p.1 ^ n)) :=
    ZMod.nontrivial_iff.mpr (ne_of_gt hpow)
  have hzero : (p.1 ^ n) • (1 : ZMod (p.1 ^ n)) = 0 := by
    simp [nsmul_eq_mul]
  exact (one_ne_zero : (1 : ZMod (p.1 ^ n)) ≠ 0)
    ((nsmul_eq_zero_iff_right (by omega : p.1 ^ n ≠ 0)).mp hzero)

/-- A p-adic quotient factor is additively torsion-free exactly for zero or
infinite exponent. The exponent-zero factor is the trivial group `ZMod 1`. -/
theorem padicQuotientFactor_isAddTorsionFree_iff (p : Nat.Primes) (e : ℕ∞) :
    IsAddTorsionFree (padicQuotientFactor.{u} p e) ↔ e = 0 ∨ e = ⊤ := by
  refine ENat.recTopCoe ?_ (fun n ↦ ?_) e
  · change IsAddTorsionFree (padicQuotientFactorTop.{u} p) ↔ _
    simp [padicQuotientFactorTop_isAddTorsionFree]
  · by_cases hn : n = 0
    · subst n
      change IsAddTorsionFree (padicQuotientFactorNat.{u} p 0) ↔ _
      simp [padicQuotientFactorNat_zero_isAddTorsionFree]
    · change IsAddTorsionFree (padicQuotientFactorNat.{u} p n) ↔ _
      constructor
      · intro h
        exact False.elim ((padicQuotientFactorNat_not_isAddTorsionFree p n hn) h)
      · intro h
        simp [hn] at h

/-- The complete primewise quotient model is torsion-free precisely when every
coordinate is trivial or an entire p-adic integer factor. -/
theorem primewisePadicQuotientModel_isAddTorsionFree_iff
    (e : Nat.Primes → ℕ∞) :
    IsAddTorsionFree (primewisePadicQuotientModel.{u} e) ↔
      ∀ p, e p = 0 ∨ e p = ⊤ := by
  constructor
  · intro h p
    have hdec : DecidableEq Nat.Primes := Classical.decEq _
    have hproduct : IsAddTorsionFree (∀ q, padicQuotientFactor.{u} q (e q)) := by
      change IsAddTorsionFree (primewisePadicQuotientModel.{u} e)
      exact h
    have hinj : Function.Injective
        (AddMonoidHom.single (fun q : Nat.Primes ↦
          (padicQuotientFactor.{u} q (e q) : Type u)) p) := by
      intro x y hxy
      have := congrArg (fun g : ∀ q, padicQuotientFactor.{u} q (e q) ↦ g p) hxy
      simpa using this
    have hp : IsAddTorsionFree (padicQuotientFactor.{u} p (e p)) :=
      hinj.isAddTorsionFree (AddMonoidHom.single (fun q : Nat.Primes ↦
        (padicQuotientFactor.{u} q (e q) : Type u)) p)
    exact (padicQuotientFactor_isAddTorsionFree_iff p (e p)).mp hp
  · intro he
    have hfactor : ∀ p, IsAddTorsionFree (padicQuotientFactor.{u} p (e p)) :=
      fun p ↦ (padicQuotientFactor_isAddTorsionFree_iff p (e p)).mpr (he p)
    change IsAddTorsionFree (∀ p, padicQuotientFactor.{u} p (e p))
    infer_instance

/-- A surjective continuous image of the primewise p-adic group is torsion-free
exactly when every exponent of its kernel quotient is zero or infinite. The
target need not be assumed commutative. -/
theorem primewisePadicSurjective_isMulTorsionFree_iff
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Function.Surjective f) :
    IsMulTorsionFree Y ↔
      ∀ p, primewisePadicKernelExponents f p = 0 ∨
        primewisePadicKernelExponents f p = ⊤ := by
  let equiv := primewisePadicContinuousMulEquivModel f hf
  constructor
  · intro h
    have htarget : IsMulTorsionFree Y := h
    have hmodel : IsMulTorsionFree
        (Multiplicative (primewisePadicQuotientModel
          (primewisePadicKernelExponents f))) :=
      equiv.symm.injective.isMulTorsionFree equiv.symm.toMonoidHom
    have hadd : IsAddTorsionFree
        (primewisePadicQuotientModel (primewisePadicKernelExponents f)) := by
      change IsAddTorsionFree (Additive (Multiplicative
        (primewisePadicQuotientModel (primewisePadicKernelExponents f))))
      infer_instance
    exact (primewisePadicQuotientModel_isAddTorsionFree_iff
      (primewisePadicKernelExponents f)).mp hadd
  · intro he
    have hadd : IsAddTorsionFree
        (primewisePadicQuotientModel (primewisePadicKernelExponents f)) :=
      (primewisePadicQuotientModel_isAddTorsionFree_iff
        (primewisePadicKernelExponents f)).mpr he
    have hmul : IsMulTorsionFree
        (Multiplicative (primewisePadicQuotientModel
          (primewisePadicKernelExponents f))) := inferInstance
    exact equiv.injective.isMulTorsionFree equiv.toMonoidHom

/-- A profinite group with a supplied topological generator is torsion-free
exactly when its generator-dependent primewise quotient exponents are zero or
infinite. -/
theorem isMulTorsionFree_iff_exponentsOfGenerator
    (G : ProfiniteGrp.{u}) (g : G) (hg : IsTopologicalGenerator G g) :
    IsMulTorsionFree G ↔
      ∀ p, primewisePadicExponentsOfGenerator G g p = 0 ∨
        primewisePadicExponentsOfGenerator G g p = ⊤ := by
  exact primewisePadicSurjective_isMulTorsionFree_iff
    (primewisePadicMapOfGenerator G g)
    (primewisePadicMapOfGenerator_surjective G g hg)

end ProfiniteGrp
