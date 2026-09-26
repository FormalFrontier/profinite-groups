/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicInvariant

/-!
# Realizing primewise exponent families

The existing product of p-adic and finite residue factors realizes every
primewise exponent family. Its canonical map is the quotient by the ideal
specified by that family; the image of the integral diagonal is a topological
generator. The resulting exponents are independent of the generator chosen.

For an all-zero family the quotient is trivial, so the *images* of zero and
one in it coincide; the original integers zero and one remain distinct.
-/

@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The multiplicative presentation of the existing additive product model. -/
noncomputable abbrev primewisePadicProcyclicModel (e : Nat.Primes → ℕ∞) :
    ProfiniteGrp.{u} :=
  ProfiniteGrp.of (Multiplicative (primewisePadicQuotientModel.{u} e))

/-- The continuous projection onto the quotient by a primewise exponent ideal,
followed by the existing quotient-to-product equivalence. -/
noncomputable def primewisePadicRealizationMap (e : Nat.Primes → ℕ∞) :
    primewisePadic.{u} →ₜ* primewisePadicProcyclicModel.{u} e := by
  let projection : Multiplicative primewisePadicRing.{u} →ₜ*
      Multiplicative (primewisePadicRing.{u} ⧸ primewisePadicIdealOfExponents e) :=
    ⟨((Ideal.Quotient.mk (primewisePadicIdealOfExponents e)).toAddMonoidHom.toMultiplicative),
      (continuous_ofAdd.comp (QuotientAddGroup.continuous_mk.comp continuous_toAdd))⟩
  exact ((primewisePadicQuotientContinuousAddEquivModel e).toMultiplicative :
    _ →ₜ* _).comp (projection.comp (primewisePadicRingMultiplicativeEquiv.symm : _ →ₜ* _))

/-- The canonical map sends a ring representative to its quotient class in the
mixed product model. -/
@[simp]
theorem primewisePadicRealizationMap_apply (e : Nat.Primes → ℕ∞)
    (x : primewisePadicRing.{u}) :
    primewisePadicRealizationMap e
        (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) =
      Multiplicative.ofAdd
        (primewisePadicQuotientContinuousAddEquivModel e
          (Ideal.Quotient.mk (primewisePadicIdealOfExponents e) x)) :=
  rfl

/-- Each coordinate of the canonical map comes from its original factor quotient. -/
@[simp]
theorem primewisePadicRealizationMap_apply_coordinate (e : Nat.Primes → ℕ∞)
    (x : primewisePadicRing.{u}) (p : Nat.Primes) :
    ((primewisePadicRealizationMap e
      (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x))).toAdd) p =
      liftedPadicQuotientContinuousAddEquivFactor p (e p)
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p (e p)) (x p)) := by
  rw [primewisePadicRealizationMap_apply]
  exact primewisePadicQuotientContinuousAddEquivModel_mk_apply e x p

/-- Integral inputs produce their own residue or p-adic coordinate class. -/
@[simp]
theorem primewisePadicRealizationMap_diagonal_coordinate
    (e : Nat.Primes → ℕ∞) (n : ℤ) (p : Nat.Primes) :
    ((primewisePadicRealizationMap.{u} e (primewisePadicDiagonal n)).toAdd) p =
      liftedPadicQuotientContinuousAddEquivFactor p (e p)
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p (e p))
          (ULift.up (n : ℤ_[p.1]))) := by
  have h : primewisePadicDiagonal.{u} n =
      primewisePadicRingMultiplicativeEquiv
        (Multiplicative.ofAdd (fun p : Nat.Primes ↦ ULift.up (n : ℤ_[p.1]))) := rfl
  rw [h, primewisePadicRealizationMap_apply_coordinate]

/-- At an infinite exponent, the image of an integer is its p-adic cast. -/
theorem primewisePadicRealizationMap_diagonal_top_coordinate
    (e : Nat.Primes → ℕ∞) (n : ℤ) (p : Nat.Primes) (hp : e p = ⊤) :
    HEq ((primewisePadicRealizationMap.{u} e (primewisePadicDiagonal n)).toAdd p)
      (ULift.up (n : ℤ_[p.1])) := by
  refine (heq_of_eq (primewisePadicRealizationMap_diagonal_coordinate.{u} e n p)).trans ?_
  let predicate (exponent : ℕ∞) : Prop :=
    HEq (liftedPadicQuotientContinuousAddEquivFactor.{u} p exponent
      (Ideal.Quotient.mk (liftedPadicIdealOfExponent p exponent)
        (ULift.up (n : ℤ_[p.1])))) (ULift.up (n : ℤ_[p.1]))
  change predicate (e p)
  have h : predicate ⊤ :=
    heq_of_eq (liftedPadicQuotientContinuousAddEquivFactor_top_mk p _)
  exact Eq.mpr (congrArg predicate hp) h

/-- At a finite exponent, the image of an integer is reduced modulo `p ^ k`. -/
theorem primewisePadicRealizationMap_diagonal_natCast_coordinate
    (e : Nat.Primes → ℕ∞) (n : ℤ) (p : Nat.Primes)
    (k : ℕ) (hp : e p = (k : ℕ∞)) :
    HEq ((primewisePadicRealizationMap.{u} e (primewisePadicDiagonal n)).toAdd p)
      (ULift.up (PadicInt.toZModPow k (n : ℤ_[p.1]))) := by
  refine (heq_of_eq (primewisePadicRealizationMap_diagonal_coordinate.{u} e n p)).trans ?_
  let predicate (exponent : ℕ∞) : Prop :=
    HEq (liftedPadicQuotientContinuousAddEquivFactor.{u} p exponent
      (Ideal.Quotient.mk (liftedPadicIdealOfExponent p exponent)
        (ULift.up (n : ℤ_[p.1]))))
      (ULift.up (PadicInt.toZModPow k (n : ℤ_[p.1])))
  change predicate (e p)
  have h : predicate (k : ℕ∞) :=
    heq_of_eq (liftedPadicQuotientContinuousAddEquivFactor_natCast_mk p k _)
  exact Eq.mpr (congrArg predicate hp) h

/-- The canonical map is onto for all exponent families. -/
theorem primewisePadicRealizationMap_surjective (e : Nat.Primes → ℕ∞) :
    Function.Surjective (primewisePadicRealizationMap.{u} e) := by
  intro y
  obtain ⟨z, rfl⟩ :=
    (primewisePadicQuotientContinuousAddEquivModel.{u} e).surjective y.toAdd
  obtain ⟨x, rfl⟩ := (Ideal.Quotient.mk_surjective z)
  exact ⟨primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x), rfl⟩

/-- The *actual* kernel of the canonical map is the chosen product ideal. -/
@[simp]
theorem primewisePadicKernelIdeal_realizationMap (e : Nat.Primes → ℕ∞) :
    primewisePadicKernelIdeal (primewisePadicRealizationMap.{u} e) =
      primewisePadicIdealOfExponents.{u} e := by
  ext x
  rw [mem_primewisePadicKernelIdeal, primewisePadicRealizationMap_apply]
  change primewisePadicQuotientContinuousAddEquivModel e
      (Ideal.Quotient.mk (primewisePadicIdealOfExponents e) x) = 0 ↔
      x ∈ primewisePadicIdealOfExponents e
  constructor
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (primewisePadicQuotientContinuousAddEquivModel e).injective
    simpa only [map_zero] using hx
  · intro hx
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- Exponents extracted from the computed kernel are precisely the input. -/
@[simp]
theorem primewisePadicKernelExponents_realizationMap (e : Nat.Primes → ℕ∞) :
    primewisePadicKernelExponents (primewisePadicRealizationMap.{u} e) = e := by
  rw [primewisePadicKernelExponents, primewisePadicKernelIdeal_realizationMap,
    primewisePadicIdealExponents_idealOfExponents]

/-- The image of the additive integral diagonal in the product model. -/
noncomputable def primewisePadicRealizationGenerator (e : Nat.Primes → ℕ∞) :
    primewisePadicProcyclicModel.{u} e :=
  primewisePadicRealizationMap.{u} e primewisePadicGenerator

/-- The generator is defined as the image of the additive *one* diagonal;
the multiplicative identity is the image of the additive zero diagonal.
These images can coincide after quotienting, in particular when all exponents are zero. -/
@[simp]
theorem primewisePadicRealizationGenerator_coordinate
    (e : Nat.Primes → ℕ∞) (p : Nat.Primes) :
    (primewisePadicRealizationGenerator.{u} e).toAdd p =
      liftedPadicQuotientContinuousAddEquivFactor p (e p)
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p (e p))
          (ULift.up (1 : ℤ_[p.1]))) := by
  exact primewisePadicRealizationMap_diagonal_coordinate e 1 p

/-- The multiplicative identity is the image of additive zero. -/
@[simp]
theorem primewisePadicRealizationMap_diagonal_zero (e : Nat.Primes → ℕ∞) :
    primewisePadicRealizationMap.{u} e (primewisePadicDiagonal 0) = 1 := by
  have h : primewisePadicDiagonal.{u} 0 = 1 := by
    funext p
    apply Multiplicative.toAdd.injective
    rfl
  rw [h, map_one]

/-- The image of an integral diagonal element is the corresponding integral
power of the realized generator, including the trivial all-zero quotient. -/
@[simp]
theorem primewisePadicRealizationMap_diagonal (e : Nat.Primes → ℕ∞) (n : ℤ) :
    primewisePadicRealizationMap.{u} e (primewisePadicDiagonal n) =
      primewisePadicRealizationGenerator.{u} e ^ n := by
  have hdiag : primewisePadicDiagonal.{u} n = primewisePadicGenerator.{u} ^ n := by
    funext p
    exact (primewisePadicGenerator_zpow n p).symm
  rw [hdiag]
  exact map_zpow (primewisePadicRealizationMap e) primewisePadicGenerator n

/-- The explicit image of the diagonal generates the entire product model. -/
theorem primewisePadicRealizationGenerator_isTopologicalGenerator
    (e : Nat.Primes → ℕ∞) :
    IsTopologicalGenerator (primewisePadicProcyclicModel.{u} e)
      (primewisePadicRealizationGenerator e) :=
  primewisePadicGenerator_isTopologicalGenerator.map
    (primewisePadicRealizationMap e) (primewisePadicRealizationMap_surjective e)

/-- The model is genuinely procyclic, including all finite, top, zero and mixed families. -/
theorem primewisePadicProcyclicModel_isProcyclic (e : Nat.Primes → ℕ∞) :
    IsProcyclic (primewisePadicProcyclicModel.{u} e) :=
  ⟨primewisePadicRealizationGenerator e,
    primewisePadicRealizationGenerator_isTopologicalGenerator e⟩

/-- The generator-induced map agrees with the quotient map, since both agree
on the dense integral diagonal. -/
theorem primewisePadicMapOfRealizationGenerator (e : Nat.Primes → ℕ∞) :
    primewisePadicMapOfGenerator (primewisePadicProcyclicModel.{u} e)
      (primewisePadicRealizationGenerator e) = primewisePadicRealizationMap e := by
  apply ContinuousMonoidHom.ext
  have h := (denseRange_primewisePadicDiagonal.{u}).equalizer
    (primewisePadicMapOfGenerator
      (primewisePadicProcyclicModel.{u} e)
      (primewisePadicRealizationGenerator e)).continuous_toFun
    (primewisePadicRealizationMap e).continuous_toFun
    (by
      funext n
      change primewisePadicMapOfGenerator _ _ (primewisePadicDiagonal n) =
        primewisePadicRealizationMap e (primewisePadicDiagonal n)
      rw [primewisePadicMapOfGenerator_diagonal,
        primewisePadicRealizationMap_diagonal])
  exact congrFun h

/-- Every procyclicity proof of the model has the prescribed invariant. -/
@[simp]
theorem primewisePadicProcyclicModel_exponents
    (e : Nat.Primes → ℕ∞)
    (h : IsProcyclic (primewisePadicProcyclicModel.{u} e)) :
    h.exponents = e := by
  rw [h.exponents_eq_of_generator _
    (primewisePadicRealizationGenerator_isTopologicalGenerator e),
    primewisePadicExponentsOfGenerator,
    primewisePadicMapOfRealizationGenerator,
    primewisePadicKernelExponents_realizationMap]

/-- Every primewise exponent family is realized in any requested universe. -/
theorem exists_procyclic_of_exponents (e : Nat.Primes → ℕ∞) :
    ∃ (G : ProfiniteGrp.{u}) (hG : IsProcyclic G), hG.exponents = e :=
  ⟨primewisePadicProcyclicModel e,
    primewisePadicProcyclicModel_isProcyclic e,
    primewisePadicProcyclicModel_exponents e _⟩

/-- Models in independent universes are continuously equivalent exactly
when their primewise exponents agree. -/
theorem primewisePadicProcyclicModel_nonempty_equiv_iff
    (e f : Nat.Primes → ℕ∞) :
    Nonempty (primewisePadicProcyclicModel.{u} e ≃ₜ*
      primewisePadicProcyclicModel.{v} f) ↔ e = f := by
  simpa only [primewisePadicProcyclicModel_exponents] using
    isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq
      (primewisePadicProcyclicModel.{u} e)
      (primewisePadicProcyclicModel.{v} f)
      (primewisePadicProcyclicModel_isProcyclic e)
      (primewisePadicProcyclicModel_isProcyclic f)

end ProfiniteGrp
