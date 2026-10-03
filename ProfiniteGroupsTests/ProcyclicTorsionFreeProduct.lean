/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicTorsionFreeProduct
public import ProfiniteGroups.ProcyclicRealization

/-!
# Clients of the torsion-free p-adic support product

Empty, singleton, and full prime supports exercise the product and its
coordinate equations. Positive finite exponents do not satisfy the hypothesis.
-/

@[expose] public section

open ProfiniteGrp

namespace ProcyclicTorsionFreeProductTests

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private def twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩

private def threePrime : Nat.Primes := ⟨3, by decide⟩

private def singleExponent (p : Nat.Primes) : ℕ∞ :=
  if p = twoPrime then ⊤ else 0

private theorem singleExponent_zeroOrTop (p : Nat.Primes) :
    singleExponent p = 0 ∨ singleExponent p = ⊤ := by
  classical
  by_cases hp : p = twoPrime
  · right
    simp [singleExponent, hp]
  · left
    simp [singleExponent, hp]

private theorem singleExponent_three_zero : singleExponent threePrime = 0 := by
  have hp : threePrime ≠ twoPrime := by decide
  simp [singleExponent, hp]

private theorem singletonSupport_two_top :
    (primewisePadicProcyclicModel_isProcyclic.{1} singleExponent).exponents twoPrime = ⊤ := by
  rw [primewisePadicProcyclicModel_exponents]
  simp [singleExponent]

private theorem singletonSupport_three_zero :
    (primewisePadicProcyclicModel_isProcyclic.{1} singleExponent).exponents threePrime = 0 := by
  rw [primewisePadicProcyclicModel_exponents]
  exact singleExponent_three_zero

private noncomputable def singletonModelPoint :
    Multiplicative (primewisePadicQuotientModel.{0}
      (primewisePadicProcyclicModel_isProcyclic.{1} singleExponent).exponents) :=
  Multiplicative.ofAdd
    (primewisePadicQuotientContinuousAddEquivModel.{0}
      (primewisePadicProcyclicModel_isProcyclic.{1} singleExponent).exponents
      (Ideal.Quotient.mk
        (primewisePadicIdealOfExponents
          (primewisePadicProcyclicModel_isProcyclic.{1} singleExponent).exponents)
        (1 : primewisePadicRing.{0})))

private theorem model_isMulTorsionFree (e : Nat.Primes → ℕ∞)
    (he : ∀ p, e p = 0 ∨ e p = ⊤) :
    IsMulTorsionFree (primewisePadicProcyclicModel.{1} e) := by
  have hfree : IsAddTorsionFree (primewisePadicQuotientModel.{1} e) :=
    (primewisePadicQuotientModel_isAddTorsionFree_iff e).mpr he
  change IsMulTorsionFree (Multiplicative (primewisePadicQuotientModel.{1} e))
  exact ⟨fun _ hn ↦ hfree.nsmul_right_injective hn⟩

/-- The inverse of an empty-support model has zero in every prime coordinate. -/
example (x : primewisePadicQuotientModel.{1} (fun _ ↦ 0)) : x = 0 := by
  apply funext
  intro p
  have h := primewisePadicQuotientModelContinuousAddEquivTopSupport_symm_apply_zero
    (fun _ ↦ 0) (fun _ ↦ Or.inl rfl)
    (primewisePadicQuotientModelContinuousAddEquivTopSupport
      (fun _ ↦ 0) (fun _ ↦ Or.inl rfl) x) p rfl
  have hp : x p = (0 : padicQuotientFactor.{1} p 0) := by
    simpa only [ContinuousAddEquiv.symm_apply_apply] using h
  exact hp

private theorem zeroExponent_support_isEmpty : IsEmpty {p : Nat.Primes //
    (primewisePadicProcyclicModel_isProcyclic.{1} (fun _ ↦ 0)).exponents p = ⊤} := by
  refine ⟨fun p ↦ ?_⟩
  have hp := congrFun (primewisePadicProcyclicModel_exponents
    (fun _ ↦ 0) (primewisePadicProcyclicModel_isProcyclic.{1} (fun _ ↦ 0))) p.1
  exact (by decide : (0 : ℕ∞) ≠ ⊤) (hp.symm.trans p.2)

/-- The empty support makes the procyclic group model subsingleton. -/
example : Subsingleton (primewisePadicProcyclicModel.{1} (fun _ ↦ 0)) := by
  let hG := primewisePadicProcyclicModel_isProcyclic.{1} (fun _ ↦ 0)
  let equiv := hG.continuousMulEquivTopSupport
    (model_isMulTorsionFree (fun _ ↦ 0) (fun _ ↦ Or.inl rfl))
  let hsupport := zeroExponent_support_isEmpty
  exact ⟨fun x y ↦ equiv.injective (funext fun p ↦ (hsupport.false p).elim)⟩

/-- The singleton-support inverse inserts its only nontrivial coordinate. -/
example :
    primewisePadicQuotientModelContinuousAddEquivTopSupport singleExponent
        singleExponent_zeroOrTop
        ((primewisePadicQuotientModelContinuousAddEquivTopSupport
          singleExponent singleExponent_zeroOrTop).symm
          (fun p ↦ ULift.up (1 : ℤ_[p.1])))
        ⟨twoPrime, by simp [singleExponent]⟩ = ULift.up (1 : ℤ_[2]) := by
  rw [primewisePadicQuotientModelContinuousAddEquivTopSupport_apply,
    primewisePadicQuotientModelContinuousAddEquivTopSupport_symm_apply]
  simp; rfl

/-- The singleton-support inverse gives zero away from its selected prime. -/
example :
    ((primewisePadicQuotientModelContinuousAddEquivTopSupport
      singleExponent singleExponent_zeroOrTop).symm
      (fun p ↦ ULift.up (1 : ℤ_[p.1]))) ⟨3, by decide⟩ = 0 := by
  apply primewisePadicQuotientModelContinuousAddEquivTopSupport_symm_apply_zero
  simp only [singleExponent]
  split_ifs with heq
  · have hvalue := congrArg Subtype.val heq
    norm_num [twoPrime] at hvalue
  · rfl

/-- Zero is also inserted at the omitted prime in multiplicative notation. -/
example :
    (((primewisePadicQuotientModelContinuousMulEquivTopSupport
      singleExponent singleExponent_zeroOrTop).symm
      (Multiplicative.ofAdd (fun p ↦ ULift.up (1 : ℤ_[p.1])))).toAdd) threePrime = 0 := by
  exact primewisePadicQuotientModelContinuousMulEquivTopSupport_symm_apply_zero
    singleExponent singleExponent_zeroOrTop _ threePrime singleExponent_three_zero

/-- For full support, a quotient representative retains its original
p-adic coordinate. -/
example (x : primewisePadicRing.{1}) (p : Nat.Primes) :
    primewisePadicQuotientModelContinuousAddEquivTopSupport (fun _ ↦ ⊤)
        (fun _ ↦ Or.inr rfl)
        (primewisePadicQuotientContinuousAddEquivModel (fun _ ↦ ⊤)
          (Ideal.Quotient.mk (primewisePadicIdealOfExponents (fun _ ↦ ⊤)) x))
        ⟨p, rfl⟩ = x p := by
  rw [primewisePadicQuotientModelContinuousAddEquivTopSupport_apply,
    primewisePadicQuotientContinuousAddEquivModel_mk_apply,
    liftedPadicQuotientContinuousAddEquivFactor_top_mk]
  rfl

/-- From the all-primes singleton model, the group equivalence reads the
nonzero retained 2-adic coordinate after transporting it to the group. -/
example :
    ((primewisePadicProcyclicModel_isProcyclic singleExponent).continuousMulEquivTopSupport
      (model_isMulTorsionFree singleExponent singleExponent_zeroOrTop)
      ((primewisePadicProcyclicModel_isProcyclic singleExponent).continuousMulEquivModel.symm
        singletonModelPoint)).toAdd
      ⟨twoPrime, singletonSupport_two_top⟩ = ULift.up (1 : ℤ_[2]) := by
  rw [IsProcyclic.continuousMulEquivTopSupport_apply,
    ContinuousMulEquiv.apply_symm_apply]
  rw [singletonModelPoint, toAdd_ofAdd,
    primewisePadicQuotientContinuousAddEquivModel_mk_apply]
  exact padicQuotientFactorContinuousAddEquivTop_mk twoPrime _
    singletonSupport_two_top ((1 : primewisePadicRing.{0}) twoPrime)

/-- The group inverse reads the retained 2-adic coordinate in its
generator-dependent all-primes model, across universes. -/
example :
    (((primewisePadicProcyclicModel_isProcyclic singleExponent).continuousMulEquivModel
      (((primewisePadicProcyclicModel_isProcyclic singleExponent).continuousMulEquivTopSupport
        (model_isMulTorsionFree singleExponent singleExponent_zeroOrTop)).symm
        (Multiplicative.ofAdd (fun p ↦ ULift.up (1 : ℤ_[p.1]))))).toAdd) twoPrime =
      (padicQuotientFactorContinuousAddEquivTop twoPrime
        ((primewisePadicProcyclicModel_isProcyclic.{1} singleExponent).exponents twoPrime)
        singletonSupport_two_top).symm (ULift.up (1 : ℤ_[2])) := by
  exact IsProcyclic.continuousMulEquivTopSupport_symm_apply
    (primewisePadicProcyclicModel_isProcyclic singleExponent)
    (model_isMulTorsionFree singleExponent singleExponent_zeroOrTop)
    _ ⟨twoPrime, singletonSupport_two_top⟩

/-- The group inverse inserts zero at the omitted prime 3. -/
example :
    (((primewisePadicProcyclicModel_isProcyclic singleExponent).continuousMulEquivModel
      (((primewisePadicProcyclicModel_isProcyclic singleExponent).continuousMulEquivTopSupport
        (model_isMulTorsionFree singleExponent singleExponent_zeroOrTop)).symm
        (Multiplicative.ofAdd (fun p ↦ ULift.up (1 : ℤ_[p.1]))))).toAdd) threePrime =
      0 := by
  exact IsProcyclic.continuousMulEquivTopSupport_symm_apply_zero
    (primewisePadicProcyclicModel_isProcyclic singleExponent)
    (model_isMulTorsionFree singleExponent singleExponent_zeroOrTop)
    _ threePrime singletonSupport_three_zero

/-- Positive finite exponents are excluded, not silently removed. -/
example : ¬ ∀ p, (fun _ : Nat.Primes ↦ (2 : ℕ∞)) p = 0 ∨
    (fun _ : Nat.Primes ↦ (2 : ℕ∞)) p = ⊤ := by
  intro h
  have htwo := h twoPrime
  norm_num at htwo

end ProcyclicTorsionFreeProductTests
