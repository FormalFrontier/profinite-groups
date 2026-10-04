/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicTorsionFreeProduct

/-!
# The support product of a procyclic profinite group

An arbitrary primewise exponent family has two disjoint nonzero supports:
positive finite exponents, whose coordinates are finite residue rings, and
infinite exponents, whose coordinates are p-adic integers. Both supports can
be infinite. Zero-exponent factors are omitted from the product.

The continuous support-product equivalence splits the quotient model into
finite and infinite factors. Its forward and inverse coordinate equations
identify the retained quotient-model coordinates with their support-product
counterparts. The inverse fills omitted zero-exponent coordinates with zero.

The exponent family of a procyclic profinite group is independent of its
generator. The equivalence from the group to its support product uses a
chosen topological generator and is not canonical without that choice.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (finite-cyclic and p-adic product description); omission of zero exponents is
  explicit here.
- Mathlib, `PadicInt.toZModPow`, `ZMod` and dependent-product topology used by
  `ProcyclicTorsionFreeProduct` and `PrimewisePadicQuotients`.
-/

@[expose] public section

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The product of residue rings at positive finite exponents and p-adic
integers at infinite exponents. The index types need not be finite. -/
abbrev primewisePadicSupportProduct (e : Nat.Primes → ℕ∞) : Type u :=
  (∀ p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤},
    ULift.{u} (ZMod (p.1.1 ^ (e p.1).toNat))) ×
  (∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1])

/-- At a finite exponent, identify the factor with the corresponding
uplifted residue ring. This also works at exponent zero. -/
noncomputable def padicQuotientFactorContinuousAddEquivFinite
    (p : Nat.Primes) (exponent : ℕ∞) (hfinite : exponent < ⊤) :
    padicQuotientFactor.{u} p exponent ≃ₜ+
      ULift.{u} (ZMod (p.1 ^ exponent.toNat)) := by
  refine ENat.recTopCoe (C := fun n ↦ n < ⊤ →
      padicQuotientFactor.{u} p n ≃ₜ+ ULift.{u} (ZMod (p.1 ^ n.toNat)))
      ?_ ?_ exponent hfinite
  · intro htop
    exact ((lt_irrefl (⊤ : ℕ∞)) htop).elim
  · intro n _
    change ULift.{u} (ZMod (p.1 ^ n)) ≃ₜ+ ULift.{u} (ZMod (p.1 ^ n))
    exact ContinuousAddEquiv.refl _

/-- On a quotient representative, a finite factor reduces modulo the
corresponding prime power. -/
@[simp]
theorem padicQuotientFactorContinuousAddEquivFinite_mk
    (p : Nat.Primes) (exponent : ℕ∞) (hfinite : exponent < ⊤)
    (x : ULift.{u} ℤ_[p.1]) :
    padicQuotientFactorContinuousAddEquivFinite p exponent hfinite
      (liftedPadicQuotientContinuousAddEquivFactor p exponent
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p exponent) x)) =
      ULift.up (PadicInt.toZModPow exponent.toNat x.down) := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfinite)
  change liftedPadicQuotientContinuousAddEquivFactor p (n : ℕ∞)
    (Ideal.Quotient.mk (liftedPadicIdealOfExponent p (n : ℕ∞)) x) =
      ULift.up (PadicInt.toZModPow n x.down)
  exact liftedPadicQuotientContinuousAddEquivFactor_natCast_mk p n x

/-- Split the all-primes quotient model into its positive finite and infinite
supports, omitting the trivial factors at exponent zero. -/
noncomputable def primewisePadicQuotientModelContinuousAddEquivSupportProduct
    (e : Nat.Primes → ℕ∞) :
    primewisePadicQuotientModel.{u} e ≃ₜ+ primewisePadicSupportProduct.{u} e := by
  classical
  letI (p : {p : {q : Nat.Primes // ¬ (0 < e q ∧ e q < ⊤)} //
      ¬ e p.1 = ⊤}) :
      Subsingleton (padicQuotientFactor.{u} p.1.1 (e p.1.1)) := by
    have hp : e p.1.1 = 0 := by
      by_contra h
      exact p.1.2 ⟨(pos_iff_ne_zero).2 h, (lt_top_iff_ne_top).2 p.2⟩
    rw [hp]
    change Subsingleton (ULift.{u} (ZMod 1))
    infer_instance
  let reindex :
      (∀ p : {p : {q : Nat.Primes // ¬ (0 < e q ∧ e q < ⊤)} // e p.1 = ⊤},
        padicQuotientFactor.{u} p.1.1 (e p.1.1)) ≃ₜ+
      (∀ p : {p : Nat.Primes // e p = ⊤}, padicQuotientFactor.{u} p.1 (e p.1)) :=
    ContinuousAddEquiv.mk
      { toEquiv :=
          { toFun := fun x p ↦ x ⟨⟨p.1, by simp [p.2]⟩, p.2⟩
            invFun := fun x p ↦ x ⟨p.1.1, p.2⟩
            left_inv := fun x ↦ by funext p; rfl
            right_inv := fun x ↦ by funext p; rfl }
        map_add' := fun _ _ ↦ rfl }
      (by
        apply continuous_pi
        intro p
        exact continuous_apply
          (⟨⟨p.1, by simp [p.2]⟩, p.2⟩ :
            {p : {q : Nat.Primes // ¬ (0 < e q ∧ e q < ⊤)} // e p.1 = ⊤}))
      (by
        apply continuous_pi
        intro p
        exact continuous_apply (⟨p.1.1, p.2⟩ : {p : Nat.Primes // e p = ⊤}))
  let finite :
      (∀ p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤},
        padicQuotientFactor.{u} p.1 (e p.1)) ≃ₜ+
      (∀ p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤},
        ULift.{u} (ZMod (p.1.1 ^ (e p.1).toNat))) :=
    continuousAddEquivPiCongrRight fun
    p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤} ↦
      padicQuotientFactorContinuousAddEquivFinite p.1 (e p.1) p.2.2
  let infinite :
      (∀ p : {p : Nat.Primes // ¬ (0 < e p ∧ e p < ⊤)},
        padicQuotientFactor.{u} p.1 (e p.1)) ≃ₜ+
      (∀ p : {p : Nat.Primes // e p = ⊤}, ULift.{u} ℤ_[p.1]) :=
    ((continuousAddEquivPiSubtype
      (fun p : {p : Nat.Primes // ¬ (0 < e p ∧ e p < ⊤)} ↦ e p.1 = ⊤)
      (fun p ↦ (padicQuotientFactor.{u} p.1 (e p.1) : Type u))).trans
      reindex).trans
      (continuousAddEquivPiCongrRight fun p ↦
        padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2)
  let split : primewisePadicQuotientModel.{u} e ≃ₜ+
      (∀ p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤},
        padicQuotientFactor.{u} p.1 (e p.1)) ×
      (∀ p : {p : Nat.Primes // ¬ (0 < e p ∧ e p < ⊤)},
        padicQuotientFactor.{u} p.1 (e p.1)) :=
    continuousAddEquivPiSubtypeProd
      (fun p : Nat.Primes ↦ 0 < e p ∧ e p < ⊤)
      (fun p ↦ (padicQuotientFactor.{u} p (e p) : Type u))
  exact split.trans
    (ContinuousAddEquiv.mk (finite.toAddEquiv.prodCongr infinite.toAddEquiv)
      (finite.toHomeomorph.prodCongr infinite.toHomeomorph).continuous
      (finite.toHomeomorph.prodCongr infinite.toHomeomorph).symm.continuous)

/-- A retained finite coordinate is the residue-ring identification of the
original quotient-model coordinate. -/
@[simp]
theorem primewisePadicQuotientModelContinuousAddEquivSupportProduct_finite_apply
    (e : Nat.Primes → ℕ∞) (x : primewisePadicQuotientModel.{u} e)
    (p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤}) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct e x).1 p =
      padicQuotientFactorContinuousAddEquivFinite p.1 (e p.1) p.2.2 (x p.1) := by
  rfl

/-- A retained infinite coordinate is the p-adic identification of the
original quotient-model coordinate. -/
@[simp]
theorem primewisePadicQuotientModelContinuousAddEquivSupportProduct_top_apply
    (e : Nat.Primes → ℕ∞) (x : primewisePadicQuotientModel.{u} e)
    (p : {p : Nat.Primes // e p = ⊤}) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct e x).2 p =
      padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2 (x p.1) := by
  rfl

/-- The inverse restores a retained finite quotient-model coordinate. -/
@[simp]
theorem primewisePadicQuotientModelContinuousAddEquivSupportProduct_symm_finite_apply
    (e : Nat.Primes → ℕ∞) (x : primewisePadicSupportProduct.{u} e)
    (p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤}) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct e).symm x p.1 =
      (padicQuotientFactorContinuousAddEquivFinite p.1 (e p.1) p.2.2).symm (x.1 p) := by
  apply (padicQuotientFactorContinuousAddEquivFinite p.1 (e p.1) p.2.2).injective
  simpa only [ContinuousAddEquiv.apply_symm_apply] using
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct_finite_apply e
      ((primewisePadicQuotientModelContinuousAddEquivSupportProduct e).symm x) p).symm

/-- The inverse restores a retained infinite quotient-model coordinate. -/
@[simp]
theorem primewisePadicQuotientModelContinuousAddEquivSupportProduct_symm_top_apply
    (e : Nat.Primes → ℕ∞) (x : primewisePadicSupportProduct.{u} e)
    (p : {p : Nat.Primes // e p = ⊤}) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct e).symm x p.1 =
      (padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2).symm (x.2 p) := by
  apply (padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2).injective
  simpa only [ContinuousAddEquiv.apply_symm_apply] using
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct_top_apply e
      ((primewisePadicQuotientModelContinuousAddEquivSupportProduct e).symm x) p).symm

/-- The inverse fills a deleted zero-exponent coordinate with zero. -/
@[simp]
theorem primewisePadicQuotientModelContinuousAddEquivSupportProduct_symm_apply_zero
    (e : Nat.Primes → ℕ∞) (x : primewisePadicSupportProduct.{u} e)
    (p : Nat.Primes) (hp : e p = 0) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct e).symm x p = 0 := by
  have : Subsingleton (padicQuotientFactor.{u} p (e p)) := by
    rw [hp]
    change Subsingleton (ULift.{u} (ZMod 1))
    infer_instance
  exact this.elim _ _

/-- The split support product in multiplicative notation. -/
noncomputable def primewisePadicQuotientModelContinuousMulEquivSupportProduct
    (e : Nat.Primes → ℕ∞) :
    Multiplicative (primewisePadicQuotientModel.{u} e) ≃ₜ*
      Multiplicative (primewisePadicSupportProduct.{u} e) :=
  (primewisePadicQuotientModelContinuousAddEquivSupportProduct e).toMultiplicative

/-- Forward multiplicative finite coordinates agree with the additive split. -/
@[simp]
theorem primewisePadicQuotientModelContinuousMulEquivSupportProduct_finite_apply
    (e : Nat.Primes → ℕ∞)
    (x : Multiplicative (primewisePadicQuotientModel.{u} e))
    (p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤}) :
    ((primewisePadicQuotientModelContinuousMulEquivSupportProduct e x).toAdd).1 p =
      padicQuotientFactorContinuousAddEquivFinite p.1 (e p.1) p.2.2 (x.toAdd p.1) :=
  primewisePadicQuotientModelContinuousAddEquivSupportProduct_finite_apply e x.toAdd p

/-- Forward multiplicative infinite coordinates agree with the additive split. -/
@[simp]
theorem primewisePadicQuotientModelContinuousMulEquivSupportProduct_top_apply
    (e : Nat.Primes → ℕ∞)
    (x : Multiplicative (primewisePadicQuotientModel.{u} e))
    (p : {p : Nat.Primes // e p = ⊤}) :
    ((primewisePadicQuotientModelContinuousMulEquivSupportProduct e x).toAdd).2 p =
      padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2 (x.toAdd p.1) :=
  primewisePadicQuotientModelContinuousAddEquivSupportProduct_top_apply e x.toAdd p

/-- The inverse multiplicative split restores a finite coordinate. -/
@[simp]
theorem primewisePadicQuotientModelContinuousMulEquivSupportProduct_symm_finite_apply
    (e : Nat.Primes → ℕ∞) (x : primewisePadicSupportProduct.{u} e)
    (p : {p : Nat.Primes // 0 < e p ∧ e p < ⊤}) :
    (((primewisePadicQuotientModelContinuousMulEquivSupportProduct e).symm
      (Multiplicative.ofAdd x)).toAdd) p.1 =
      (padicQuotientFactorContinuousAddEquivFinite p.1 (e p.1) p.2.2).symm (x.1 p) :=
  primewisePadicQuotientModelContinuousAddEquivSupportProduct_symm_finite_apply e x p

/-- The inverse multiplicative split restores an infinite coordinate. -/
@[simp]
theorem primewisePadicQuotientModelContinuousMulEquivSupportProduct_symm_top_apply
    (e : Nat.Primes → ℕ∞) (x : primewisePadicSupportProduct.{u} e)
    (p : {p : Nat.Primes // e p = ⊤}) :
    (((primewisePadicQuotientModelContinuousMulEquivSupportProduct e).symm
      (Multiplicative.ofAdd x)).toAdd) p.1 =
      (padicQuotientFactorContinuousAddEquivTop p.1 (e p.1) p.2).symm (x.2 p) :=
  primewisePadicQuotientModelContinuousAddEquivSupportProduct_symm_top_apply e x p

/-- The inverse multiplicative split fills a deleted coordinate with zero. -/
@[simp]
theorem primewisePadicQuotientModelContinuousMulEquivSupportProduct_symm_apply_zero
    (e : Nat.Primes → ℕ∞) (x : primewisePadicSupportProduct.{u} e)
    (p : Nat.Primes) (hp : e p = 0) :
    (((primewisePadicQuotientModelContinuousMulEquivSupportProduct e).symm
      (Multiplicative.ofAdd x)).toAdd) p = 0 :=
  primewisePadicQuotientModelContinuousAddEquivSupportProduct_symm_apply_zero e x p hp

/-- On a zero-or-infinite exponent family, the infinite coordinates of the
support product agree with the existing p-adic support equivalence. -/
theorem primewisePadicQuotientModelContinuousAddEquivSupportProduct_topSupport
    (e : Nat.Primes → ℕ∞) (he : ∀ p, e p = 0 ∨ e p = ⊤)
    (x : primewisePadicQuotientModel.{u} e) :
    (primewisePadicQuotientModelContinuousAddEquivSupportProduct e x).2 =
      primewisePadicQuotientModelContinuousAddEquivTopSupport e he x := by
  funext p
  rw [primewisePadicQuotientModelContinuousAddEquivSupportProduct_top_apply,
    primewisePadicQuotientModelContinuousAddEquivTopSupport_apply]

namespace IsProcyclic

/-- A procyclic profinite group is continuously equivalent to the support
product of its generator-independent primewise exponents. The equivalence
uses a chosen generator; it requires no torsion-freeness assumption.

The finite-cyclic and p-adic product description comes from Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Ch. I §7, before Proposition (1.7.7); this model explicitly
omits zero exponents. -/
noncomputable def continuousMulEquivSupportProduct
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) :
    G ≃ₜ* Multiplicative (primewisePadicSupportProduct.{0} hG.exponents) :=
  hG.continuousMulEquivModel.trans
    (primewisePadicQuotientModelContinuousMulEquivSupportProduct hG.exponents)

/-- A finite coordinate of the group equivalence is the corresponding
residue coordinate of its generator-dependent all-primes model. -/
@[simp]
theorem continuousMulEquivSupportProduct_finite_apply
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) (g : G)
    (p : {p : Nat.Primes // 0 < hG.exponents p ∧ hG.exponents p < ⊤}) :
    ((hG.continuousMulEquivSupportProduct g).toAdd).1 p =
      padicQuotientFactorContinuousAddEquivFinite p.1 (hG.exponents p.1)
        p.2.2 ((hG.continuousMulEquivModel g).toAdd p.1) := by
  simpa only [continuousMulEquivSupportProduct, ContinuousMulEquiv.trans_apply] using
    primewisePadicQuotientModelContinuousMulEquivSupportProduct_finite_apply
      hG.exponents (hG.continuousMulEquivModel g) p

/-- An infinite coordinate of the group equivalence is the corresponding
p-adic coordinate of its generator-dependent all-primes model. -/
@[simp]
theorem continuousMulEquivSupportProduct_top_apply
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) (g : G)
    (p : {p : Nat.Primes // hG.exponents p = ⊤}) :
    ((hG.continuousMulEquivSupportProduct g).toAdd).2 p =
      padicQuotientFactorContinuousAddEquivTop p.1 (hG.exponents p.1)
        p.2 ((hG.continuousMulEquivModel g).toAdd p.1) := by
  simpa only [continuousMulEquivSupportProduct, ContinuousMulEquiv.trans_apply] using
    primewisePadicQuotientModelContinuousMulEquivSupportProduct_top_apply
      hG.exponents (hG.continuousMulEquivModel g) p

/-- The inverse group equivalence restores a retained finite coordinate
before returning to the original group. -/
@[simp]
theorem continuousMulEquivSupportProduct_symm_finite_apply
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G)
    (x : primewisePadicSupportProduct.{0} hG.exponents)
    (p : {p : Nat.Primes // 0 < hG.exponents p ∧ hG.exponents p < ⊤}) :
    ((hG.continuousMulEquivModel
      (hG.continuousMulEquivSupportProduct.symm (Multiplicative.ofAdd x))).toAdd) p.1 =
      (padicQuotientFactorContinuousAddEquivFinite p.1 (hG.exponents p.1) p.2.2).symm
        (x.1 p) := by
  simpa only [continuousMulEquivSupportProduct, ContinuousMulEquiv.symm_trans_apply,
    ContinuousMulEquiv.apply_symm_apply] using
    primewisePadicQuotientModelContinuousMulEquivSupportProduct_symm_finite_apply
      hG.exponents x p

/-- The inverse group equivalence restores a retained infinite coordinate
before returning to the original group. -/
@[simp]
theorem continuousMulEquivSupportProduct_symm_top_apply
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G)
    (x : primewisePadicSupportProduct.{0} hG.exponents)
    (p : {p : Nat.Primes // hG.exponents p = ⊤}) :
    ((hG.continuousMulEquivModel
      (hG.continuousMulEquivSupportProduct.symm (Multiplicative.ofAdd x))).toAdd) p.1 =
      (padicQuotientFactorContinuousAddEquivTop p.1 (hG.exponents p.1) p.2).symm
        (x.2 p) := by
  simpa only [continuousMulEquivSupportProduct, ContinuousMulEquiv.symm_trans_apply,
    ContinuousMulEquiv.apply_symm_apply] using
    primewisePadicQuotientModelContinuousMulEquivSupportProduct_symm_top_apply
      hG.exponents x p

/-- The inverse group equivalence fills each deleted coordinate with zero
in its generator-dependent all-primes model. -/
@[simp]
theorem continuousMulEquivSupportProduct_symm_apply_zero
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G)
    (x : primewisePadicSupportProduct.{0} hG.exponents)
    (p : Nat.Primes) (hp : hG.exponents p = 0) :
    ((hG.continuousMulEquivModel
      (hG.continuousMulEquivSupportProduct.symm (Multiplicative.ofAdd x))).toAdd) p = 0 := by
  simpa only [continuousMulEquivSupportProduct, ContinuousMulEquiv.symm_trans_apply,
    ContinuousMulEquiv.apply_symm_apply] using
    primewisePadicQuotientModelContinuousMulEquivSupportProduct_symm_apply_zero
      hG.exponents x p hp

/-- In the torsion-free case, the infinite part of the general group model
agrees with the p-adic support-product equivalence. -/
theorem continuousMulEquivSupportProduct_topSupport
    {G : ProfiniteGrp.{v}} (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (g : G) :
    ((hG.continuousMulEquivSupportProduct g).toAdd).2 =
      (hG.continuousMulEquivTopSupport hfree g).toAdd := by
  funext p
  rw [continuousMulEquivSupportProduct_top_apply,
    continuousMulEquivTopSupport_apply]

end IsProcyclic
end ProfiniteGrp
