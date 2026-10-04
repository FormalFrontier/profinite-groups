/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.PrimewisePadicQuotients
public import ProfiniteGroups.PrimewisePadicSubgroups

/-!
# Quotient models of profinite groups with a supplied topological generator

A continuous surjection from the primewise p-adic product identifies its
target with the multiplicative form of the quotient by its kernel ideal. The
ideal's primewise exponents then give a product of finite residue and p-adic
factors. For a profinite group with a specified topological generator, the
canonical completion map supplies the required surjection. The exponents in
this construction depend on the supplied map or generator.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (procyclic groups as quotients of the completed integers and primewise products).
- Mathlib, profinite completion and ideal-quotient APIs used by `PrimewisePadicQuotients`
  and `PrimewisePadicSubgroups`.
-/

@[expose] public section

open Function

universe u v

/-- An additive topological group equivalence is also an equivalence of the
corresponding multiplicatively written groups. -/
noncomputable def ContinuousAddEquiv.toMultiplicative
    {A : Type u} {B : Type v} [AddGroup A] [AddGroup B]
    [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ+ B) : Multiplicative A ≃ₜ* Multiplicative B := by
  let em : Multiplicative A ≃* Multiplicative B := e.toAddEquiv.toMultiplicative
  exact ContinuousMulEquiv.mk em
    (continuous_ofAdd.comp (e.continuous_toFun.comp continuous_toAdd))
    (by
      change Continuous (Multiplicative.ofAdd ∘ e.symm ∘ Multiplicative.toAdd)
      exact continuous_ofAdd.comp (e.continuous_invFun.comp continuous_toAdd))

/-- Equality of ideals identifies their quotient topological additive groups. -/
def Ideal.quotientContinuousAddEquivOfEq
    {R : Type u} [CommRing R] [TopologicalSpace R]
    {I J : Ideal R} (h : I = J) : (R ⧸ I) ≃ₜ+ (R ⧸ J) := by
  subst J
  exact ContinuousAddEquiv.refl _

/-- Equality-of-ideals transport fixes quotient representatives. -/
@[simp]
theorem Ideal.quotientContinuousAddEquivOfEq_mk
    {R : Type u} [CommRing R] [TopologicalSpace R]
    {I J : Ideal R} (h : I = J) (x : R) :
    Ideal.quotientContinuousAddEquivOfEq h (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk J x := by
  subst J
  rfl

namespace ProfiniteGrp

/-- The continuous primewise map determined by an element of a profinite
group. -/
noncomputable def primewisePadicMapOfGenerator (G : ProfiniteGrp.{u}) (g : G) :
    primewisePadic.{u} →ₜ* G :=
  (integerCompletionMap G g).hom.comp
    (integerCompletionEquivPrimewisePadic.{u}.symm :
      primewisePadic.{u} →ₜ* integerCompletion.{u})

/-- The integral diagonal maps to the corresponding power of the supplied
element. -/
@[simp]
theorem primewisePadicMapOfGenerator_diagonal
    (G : ProfiniteGrp.{u}) (g : G) (n : ℤ) :
    primewisePadicMapOfGenerator G g (primewisePadicDiagonal n) = g ^ n := by
  simp [primewisePadicMapOfGenerator]

/-- A topological generator makes the primewise map surjective. -/
theorem primewisePadicMapOfGenerator_surjective
    (G : ProfiniteGrp.{u}) (g : G) (hg : IsTopologicalGenerator G g) :
    Surjective (primewisePadicMapOfGenerator G g) := by
  exact (isTopologicalGenerator_iff_surjective_integerCompletionMap G g).mp hg
    |>.comp integerCompletionEquivPrimewisePadic.{u}.symm.surjective

/-- An additive homomorphism underlying a continuous map out of the
primewise product, with the target written additively. -/
noncomputable def primewisePadicAdditiveMap
    {Y : Type v} [Group Y] [TopologicalSpace Y]
    (f : primewisePadic.{u} →ₜ* Y) :
    primewisePadicRing.{u} →+ Additive Y :=
  ((f.comp (primewisePadicRingMultiplicativeEquiv.{u} :
    Multiplicative primewisePadicRing.{u} →ₜ* primewisePadic.{u})).toMonoidHom).toAdditiveRight

/-- The ideal attached to a map is exactly the additive kernel of its
underlying homomorphism. -/
theorem primewisePadicKernelIdeal_toAddSubgroup
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) :
    (primewisePadicKernelIdeal f).toAddSubgroup =
      (primewisePadicAdditiveMap f).ker := by
  ext x
  simp [primewisePadicAdditiveMap, AddMonoidHom.mem_ker,
    mem_primewisePadicKernelIdeal]

/-- The additive first isomorphism theorem, applied to the kernel ideal of
a surjective primewise map. -/
noncomputable def primewisePadicKernelIdealAddEquiv
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f) :
    (primewisePadicRing.{u} ⧸ primewisePadicKernelIdeal f) ≃+ Additive Y := by
  let φ := primewisePadicAdditiveMap f
  have hφ : Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := hf (Additive.toMul y)
    refine ⟨(primewisePadicRingMultiplicativeEquiv.{u}.symm x).toAdd, ?_⟩
    simpa [φ, primewisePadicAdditiveMap] using congrArg Additive.ofMul hx
  change (primewisePadicRing.{u} ⧸ (primewisePadicKernelIdeal f).toAddSubgroup) ≃+
    Additive Y
  exact (QuotientAddGroup.quotientAddEquivOfEq
    (primewisePadicKernelIdeal_toAddSubgroup f)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ)

/-- On a quotient representative, the additive equivalence agrees with the
original map. -/
@[simp]
theorem primewisePadicKernelIdealAddEquiv_mk
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f)
    (x : primewisePadicRing.{u}) :
    primewisePadicKernelIdealAddEquiv f hf
      (Ideal.Quotient.mk (primewisePadicKernelIdeal f) x) =
      Additive.ofMul (f (primewisePadicRingMultiplicativeEquiv
        (Multiplicative.ofAdd x))) := by
  change (QuotientAddGroup.quotientAddEquivOfEq
    (primewisePadicKernelIdeal_toAddSubgroup f)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (primewisePadicAdditiveMap f) _)
        (Ideal.Quotient.mk (primewisePadicKernelIdeal f) x) = _
  simp only [QuotientAddGroup.quotientKerEquivOfSurjective]
  rfl

/-- A continuous surjection from the primewise p-adic group induces a
topological group equivalence from the multiplicative kernel-ideal quotient.
Compactness of the source and Hausdorffness of the target supply continuity
of the inverse. -/
noncomputable def primewisePadicKernelIdealContinuousMulEquiv
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f) :
    Multiplicative (primewisePadicRing.{u} ⧸ primewisePadicKernelIdeal f) ≃ₜ* Y := by
  let e := primewisePadicKernelIdealAddEquiv f hf
  have he : Continuous e := by
    rw [← (QuotientRing.isOpenQuotientMap_mk
      (primewisePadicKernelIdeal f)).continuous_comp_iff]
    have hcomp : (e : (primewisePadicRing.{u} ⧸ primewisePadicKernelIdeal f) →
        Additive Y) ∘ Ideal.Quotient.mk (primewisePadicKernelIdeal f) =
        Additive.ofMul ∘ f ∘ primewisePadicRingMultiplicativeEquiv.{u} ∘
          Multiplicative.ofAdd := by
      funext x
      exact primewisePadicKernelIdealAddEquiv_mk f hf x
    rw [hcomp]
    exact continuous_ofMul.comp
      (f.continuous_toFun.comp
        (primewisePadicRingMultiplicativeEquiv.{u}.continuous_toFun.comp
          continuous_ofAdd))
  let em := e.toMultiplicativeLeft
  have hem : Continuous em := continuous_toMul.comp (he.comp continuous_toAdd)
  exact ContinuousMulEquiv.mk'
    ((isHomeomorph_iff_continuous_bijective.mpr
      ⟨hem, em.bijective⟩).homeomorph em)
    em.map_mul

/-- The kernel-ideal quotient sends a representative to its image. -/
@[simp]
theorem primewisePadicKernelIdealContinuousMulEquiv_mk
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f)
    (x : primewisePadicRing.{u}) :
    primewisePadicKernelIdealContinuousMulEquiv f hf
        (Multiplicative.ofAdd
          (Ideal.Quotient.mk (primewisePadicKernelIdeal f) x)) =
      f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) := by
  exact congrArg Additive.toMul
    (primewisePadicKernelIdealAddEquiv_mk f hf x)

/-- The inverse equivalence takes the image of a representative back to its
kernel-ideal quotient class. -/
@[simp]
theorem primewisePadicKernelIdealContinuousMulEquiv_symm_apply
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f)
    (x : primewisePadicRing.{u}) :
    (primewisePadicKernelIdealContinuousMulEquiv f hf).symm
      (f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x))) =
      Multiplicative.ofAdd
        (Ideal.Quotient.mk (primewisePadicKernelIdeal f) x) := by
  apply (primewisePadicKernelIdealContinuousMulEquiv f hf).symm_apply_eq.mpr
  exact (primewisePadicKernelIdealContinuousMulEquiv_mk f hf x).symm

/-- A surjective primewise map identifies its target with the product
model of the exponent ideal of its kernel. -/
noncomputable def primewisePadicContinuousMulEquivModel
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f) :
    Y ≃ₜ* Multiplicative (primewisePadicQuotientModel
      (primewisePadicKernelExponents f)) :=
  ((primewisePadicKernelIdealContinuousMulEquiv f hf).symm.trans
    (Ideal.quotientContinuousAddEquivOfEq
      (primewisePadicKernelIdeal_eq_idealOfExponents f)).toMultiplicative).trans
    (primewisePadicQuotientContinuousAddEquivModel
      (primewisePadicKernelExponents f)).toMultiplicative

/-- Coordinate equation for a quotient representative under the inverse
target-to-product equivalence. -/
@[simp]
theorem primewisePadicContinuousMulEquivModel_apply_mk
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (hf : Surjective f)
    (x : primewisePadicRing.{u}) (p : Nat.Primes) :
    ((primewisePadicContinuousMulEquivModel f hf)
      (f (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)))).toAdd p =
    liftedPadicQuotientContinuousAddEquivFactor p
      (primewisePadicKernelExponents f p)
      (Ideal.Quotient.mk
        (liftedPadicIdealOfExponent p (primewisePadicKernelExponents f p))
        (x p)) := by
  simp only [primewisePadicContinuousMulEquivModel, ContinuousMulEquiv.trans_apply,
    primewisePadicKernelIdealContinuousMulEquiv_symm_apply]
  change primewisePadicQuotientContinuousAddEquivModel
      (primewisePadicKernelExponents f)
      (Ideal.quotientContinuousAddEquivOfEq
        (primewisePadicKernelIdeal_eq_idealOfExponents f)
          (Ideal.Quotient.mk (primewisePadicKernelIdeal f) x)) p = _
  rw [Ideal.quotientContinuousAddEquivOfEq_mk]
  exact primewisePadicQuotientContinuousAddEquivModel_mk_apply
    (primewisePadicKernelExponents f) x p

/-- The generator-dependent primewise kernel exponents. -/
noncomputable def primewisePadicExponentsOfGenerator
    (G : ProfiniteGrp.{u}) (g : G) : Nat.Primes → ℕ∞ :=
  primewisePadicKernelExponents (primewisePadicMapOfGenerator G g)

/-- A supplied topological generator gives an explicit product model, with
no assertion that the exponent family is generator-independent.

The primewise quotient model is motivated by the procyclic classification in
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
(1.7.7). Mathlib’s profinite completion and p-adic quotient APIs supply the formal
approach. -/
noncomputable def procyclicContinuousMulEquivModel
    (G : ProfiniteGrp.{u}) (g : G) (hg : IsTopologicalGenerator G g) :
    G ≃ₜ* Multiplicative (primewisePadicQuotientModel
      (primewisePadicExponentsOfGenerator G g)) :=
  primewisePadicContinuousMulEquivModel
    (primewisePadicMapOfGenerator G g)
    (primewisePadicMapOfGenerator_surjective G g hg)

/-- The generator's powers have the expected product-model coordinates. -/
theorem procyclicContinuousMulEquivModel_zpow_apply
    (G : ProfiniteGrp.{u}) (g : G) (hg : IsTopologicalGenerator G g)
    (n : ℤ) (p : Nat.Primes) :
    ((procyclicContinuousMulEquivModel G g hg (g ^ n)).toAdd) p =
    liftedPadicQuotientContinuousAddEquivFactor p
      (primewisePadicExponentsOfGenerator G g p)
      (Ideal.Quotient.mk
        (liftedPadicIdealOfExponent p (primewisePadicExponentsOfGenerator G g p))
        ((primewisePadicRingMultiplicativeEquiv.{u}.symm
          (primewisePadicDiagonal n)).toAdd p)) := by
  rw [← primewisePadicMapOfGenerator_diagonal G g n]
  exact primewisePadicContinuousMulEquivModel_apply_mk _ _ _ _

/-- Simp-normal coordinates of an integral multiple of the model generator.
The power-coordinate theorem remains available by name; this form also applies
after `map_zpow` and `toAdd_zpow` normalize its left-hand side. -/
@[simp]
theorem procyclicContinuousMulEquivModel_zsmul_apply
    (G : ProfiniteGrp.{u}) (g : G) (hg : IsTopologicalGenerator G g)
    (n : ℤ) (p : Nat.Primes) :
    (n • (procyclicContinuousMulEquivModel G g hg g).toAdd) p =
    liftedPadicQuotientContinuousAddEquivFactor p
      (primewisePadicExponentsOfGenerator G g p)
      (Ideal.Quotient.mk
        (liftedPadicIdealOfExponent p (primewisePadicExponentsOfGenerator G g p))
        ((primewisePadicRingMultiplicativeEquiv.{u}.symm
          (primewisePadicDiagonal n)).toAdd p)) := by
  simpa only [map_zpow, toAdd_zpow] using
    procyclicContinuousMulEquivModel_zpow_apply G g hg n p

end ProfiniteGrp
