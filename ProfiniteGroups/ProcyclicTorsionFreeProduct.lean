/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicInvariant
public import ProfiniteGroups.ProcyclicTorsionFree

/-!
# The p-adic product of a torsion-free procyclic group

When the primewise quotient exponents are zero or infinite, the zero factors
can be removed. The remaining factors are p-adic integers, indexed by the
primes of infinite exponent. A torsion-free procyclic profinite group has this
product as an explicit continuous multiplicative model.

The exponent support does not depend on the choice of generator. The
equivalence from a group to its model does use a chosen topological generator;
it is not a canonical equivalence without that choice.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (torsion-free p-adic product description).
- Mathlib, `PadicInt` and dependent-product topology used by
  `ProcyclicTorsionFree` and `ProcyclicInvariant`.
-/

@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Identify an infinite-exponent factor of the primewise quotient model
with its uplifted p-adic integers. -/
noncomputable def padicQuotientFactorContinuousAddEquivTop
    (p : Nat.Primes) (e : ℕ∞) (he : e = ⊤) :
    padicQuotientFactor.{u} p e ≃ₜ+ ULift.{u} ℤ_[p.1] := by
  subst e
  change ULift.{u} ℤ_[p.1] ≃ₜ+ ULift.{u} ℤ_[p.1]
  exact ContinuousAddEquiv.refl _

/-- At infinite exponent, a quotient representative retains its p-adic coordinate. -/
@[simp]
theorem padicQuotientFactorContinuousAddEquivTop_mk
    (p : Nat.Primes) (e : ℕ∞) (he : e = ⊤) (x : ULift.{u} ℤ_[p.1]) :
    padicQuotientFactorContinuousAddEquivTop p e he
      (liftedPadicQuotientContinuousAddEquivFactor p e
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p e) x)) = x := by
  subst e
  change liftedPadicQuotientContinuousAddEquivFactor p ⊤
    (Ideal.Quotient.mk (liftedPadicIdealOfExponent p ⊤) x) = x
  exact liftedPadicQuotientContinuousAddEquivFactor_top_mk p x

/-- Delete the zero-exponent factors of a torsion-free primewise quotient
model. Its target is the product of uplifted p-adic integer factors at the
infinite-exponent primes; the support may be empty. -/
noncomputable def primewisePadicQuotientModelContinuousAddEquivTopSupport
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤) :
    primewisePadicQuotientModel.{u} e ≃ₜ+
      (∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1]) := by
  classical
  letI (p : {p : Nat.Primes // ¬ e p = ⊤}) :
      Subsingleton (padicQuotientFactor.{u} p.1 (e p.1)) := by
    have hp : e p.1 = 0 := (he p.1).resolve_right p.2
    rw [hp]
    change Subsingleton (ULift.{u} (ZMod 1))
    infer_instance
  exact (continuousAddEquivPiSubtype (fun p ↦ e p = ⊤)
    (fun p ↦ (padicQuotientFactor.{u} p (e p) : Type u))).trans
      (continuousAddEquivPiCongrRight fun p ↦
        padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2)

/-- At a retained prime, the forward equivalence applies the infinite-factor
identification to the original model coordinate. -/
@[simp]
theorem primewisePadicQuotientModelContinuousAddEquivTopSupport_apply
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤)
    (x : primewisePadicQuotientModel.{u} e)
    (p : {p : Nat.Primes // e p = ⊤}) :
    primewisePadicQuotientModelContinuousAddEquivTopSupport e he x p =
      padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2 (x p.1) := by
  rfl

/-- The inverse inserts the p-adic integer at each retained prime. -/
@[simp]
theorem primewisePadicQuotientModelContinuousAddEquivTopSupport_symm_apply
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤)
    (x : ∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1])
    (p : {p : Nat.Primes // e p = ⊤}) :
    (primewisePadicQuotientModelContinuousAddEquivTopSupport e he).symm x p.1 =
      (padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2).symm (x p) := by
  apply (padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2).injective
  simpa only [ContinuousAddEquiv.apply_symm_apply] using
    (primewisePadicQuotientModelContinuousAddEquivTopSupport_apply e he
      ((primewisePadicQuotientModelContinuousAddEquivTopSupport e he).symm x) p).symm

/-- The inverse fills every omitted zero-exponent coordinate with zero. -/
@[simp]
theorem primewisePadicQuotientModelContinuousAddEquivTopSupport_symm_apply_zero
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤)
    (x : ∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1])
    (p : Nat.Primes) (hp : e p = 0) :
    (primewisePadicQuotientModelContinuousAddEquivTopSupport e he).symm x p = 0 := by
  have : Subsingleton (padicQuotientFactor.{u} p (e p)) := by
    rw [hp]
    change Subsingleton (ULift.{u} (ZMod 1))
    infer_instance
  exact this.elim _ _

/-- The same zero-or-infinite exponent support product in multiplicative
notation, for use with profinite groups. -/
noncomputable def primewisePadicQuotientModelContinuousMulEquivTopSupport
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤) :
    Multiplicative (primewisePadicQuotientModel.{u} e) ≃ₜ*
      Multiplicative (∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1]) :=
  (primewisePadicQuotientModelContinuousAddEquivTopSupport e he).toMultiplicative

/-- Forward multiplicative coordinates agree with the additive model. -/
@[simp]
theorem primewisePadicQuotientModelContinuousMulEquivTopSupport_apply
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤)
    (x : Multiplicative (primewisePadicQuotientModel.{u} e))
    (p : {p : Nat.Primes // e p = ⊤}) :
    ((primewisePadicQuotientModelContinuousMulEquivTopSupport e he x).toAdd) p =
      padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2 (x.toAdd p.1) :=
  primewisePadicQuotientModelContinuousAddEquivTopSupport_apply e he x.toAdd p

/-- The inverse multiplicative equivalence restores each retained
coordinate of the original all-primes model. -/
@[simp]
theorem primewisePadicQuotientModelContinuousMulEquivTopSupport_symm_apply
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤)
    (x : ∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1])
    (p : {p : Nat.Primes // e p = ⊤}) :
    (((primewisePadicQuotientModelContinuousMulEquivTopSupport e he).symm
      (Multiplicative.ofAdd x)).toAdd) p.1 =
      (padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2).symm (x p) :=
  primewisePadicQuotientModelContinuousAddEquivTopSupport_symm_apply e he x p

/-- The inverse multiplicative equivalence fills each omitted coordinate
of the all-primes model with the identity. -/
@[simp]
theorem primewisePadicQuotientModelContinuousMulEquivTopSupport_symm_apply_zero
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤)
    (x : ∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1])
    (p : Nat.Primes) (hp : e p = 0) :
    (((primewisePadicQuotientModelContinuousMulEquivTopSupport e he).symm
      (Multiplicative.ofAdd x)).toAdd) p = 0 :=
  primewisePadicQuotientModelContinuousAddEquivTopSupport_symm_apply_zero e he x p hp

namespace IsProcyclic

/-- A torsion-free procyclic profinite group is continuously equivalent to
the product of p-adic integers indexed by its infinite-exponent primes.
The support is generator-independent, but the equivalence uses a chosen
topological generator.

The torsion-free p-adic product is described in Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Ch. I §7, before Proposition (1.7.7). -/
noncomputable def continuousMulEquivTopSupport
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) (hfree : IsMulTorsionFree G) :
    G ≃ₜ* Multiplicative
      (∀ p : {p : Nat.Primes // hG.exponents p = ⊤}, ULift.{0} ℤ_[p.1]) :=
  hG.continuousMulEquivModel.trans
    (primewisePadicQuotientModelContinuousMulEquivTopSupport hG.exponents
      ((primewisePadicSurjective_isMulTorsionFree_iff
        (primewisePadicBaseMapOfGenerator G hG.choose)
        (primewisePadicBaseMapOfGenerator_surjective G hG.choose hG.choose_spec)).mp
          hfree))

/-- Coordinates of the group equivalence are the coordinates of its
generator-dependent primewise model, with the zero factors omitted. -/
@[simp]
theorem continuousMulEquivTopSupport_apply
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (g : G) (p : {p : Nat.Primes // hG.exponents p = ⊤}) :
    ((hG.continuousMulEquivTopSupport hfree g).toAdd) p =
      padicQuotientFactorContinuousAddEquivTop p.1 (hG.exponents p.1) p.2
        ((hG.continuousMulEquivModel g).toAdd p.1) := by
  have he : ∀ q, hG.exponents q = 0 ∨ hG.exponents q = ⊤ :=
    (primewisePadicSurjective_isMulTorsionFree_iff
      (primewisePadicBaseMapOfGenerator G hG.choose)
      (primewisePadicBaseMapOfGenerator_surjective G hG.choose hG.choose_spec)).mp
        hfree
  simpa only [continuousMulEquivTopSupport, ContinuousMulEquiv.trans_apply] using
    primewisePadicQuotientModelContinuousMulEquivTopSupport_apply hG.exponents he
      (hG.continuousMulEquivModel g) p

/-- The inverse group equivalence restores a retained p-adic coordinate
in the all-primes model before returning to the original group. -/
@[simp]
theorem continuousMulEquivTopSupport_symm_apply
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (x : ∀ p : {p : Nat.Primes // hG.exponents p = ⊤}, ULift.{0} ℤ_[p.1])
    (p : {p : Nat.Primes // hG.exponents p = ⊤}) :
    ((hG.continuousMulEquivModel
      ((hG.continuousMulEquivTopSupport hfree).symm (Multiplicative.ofAdd x))).toAdd) p.1 =
      (padicQuotientFactorContinuousAddEquivTop p.1 (hG.exponents p.1) p.2).symm
        (x p) := by
  have he : ∀ q, hG.exponents q = 0 ∨ hG.exponents q = ⊤ :=
    (primewisePadicSurjective_isMulTorsionFree_iff
      (primewisePadicBaseMapOfGenerator G hG.choose)
      (primewisePadicBaseMapOfGenerator_surjective G hG.choose hG.choose_spec)).mp
        hfree
  simpa only [continuousMulEquivTopSupport, ContinuousMulEquiv.symm_trans_apply,
    ContinuousMulEquiv.apply_symm_apply] using
    primewisePadicQuotientModelContinuousMulEquivTopSupport_symm_apply
      hG.exponents he x p

/-- In the generator-dependent all-primes model, the inverse group
equivalence fills every omitted zero-exponent coordinate with the identity. -/
@[simp]
theorem continuousMulEquivTopSupport_symm_apply_zero
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (x : ∀ p : {p : Nat.Primes // hG.exponents p = ⊤}, ULift.{0} ℤ_[p.1])
    (p : Nat.Primes) (hp : hG.exponents p = 0) :
    ((hG.continuousMulEquivModel
      ((hG.continuousMulEquivTopSupport hfree).symm (Multiplicative.ofAdd x))).toAdd) p =
      0 := by
  have he : ∀ q, hG.exponents q = 0 ∨ hG.exponents q = ⊤ :=
    (primewisePadicSurjective_isMulTorsionFree_iff
      (primewisePadicBaseMapOfGenerator G hG.choose)
      (primewisePadicBaseMapOfGenerator_surjective G hG.choose hG.choose_spec)).mp
        hfree
  simpa only [continuousMulEquivTopSupport, ContinuousMulEquiv.symm_trans_apply,
    ContinuousMulEquiv.apply_symm_apply] using
    primewisePadicQuotientModelContinuousMulEquivTopSupport_symm_apply_zero
      hG.exponents he x p hp

end IsProcyclic
end ProfiniteGrp
