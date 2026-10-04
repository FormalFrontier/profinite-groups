/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.PrimewisePadicIdeals

/-!
# Closed subgroups of the primewise p-adic product

Closed additive subgroups of `ProfiniteGrp.primewisePadicRing` are ideals,
because the diagonal integer casts are dense.  Consequently they are
classified by their coordinatewise `ℕ∞` exponents.  This file packages the
classification as an order isomorphism (with the exponent order reversed),
transports it to closed multiplicative subgroups of
`ProfiniteGrp.primewisePadic`, and applies it to kernels of continuous
multiplicative homomorphisms into arbitrary T1 targets.

## References

- Mathlib, `Ideal.map_mono`, `Ideal.map_evalRingHom_pi` and closed subgroups;
  `PrimewisePadicIdeals` supplies the product-ideal exponent classification.
-/

@[expose] public section

open Function Set

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Inclusion of primewise p-adic product ideals is reverse pointwise
comparison of their exponent families. -/
theorem primewisePadicIdealOfExponents_le_iff
    {e d : Nat.Primes → ℕ∞} :
    primewisePadicIdealOfExponents.{u} e ≤
        primewisePadicIdealOfExponents d ↔
      ∀ p, d p ≤ e p := by
  constructor
  · intro h p
    have hp := Ideal.map_mono (f := Pi.evalRingHom
      (fun q : Nat.Primes ↦ ULift.{u} ℤ_[q.1]) p) h
    unfold primewisePadicIdealOfExponents at hp
    rw [Ideal.map_evalRingHom_pi, Ideal.map_evalRingHom_pi] at hp
    change OrderDual.toDual (e p) ≤ OrderDual.toDual (d p)
    exact (liftedPadicIdealOrderIso p).symm.le_iff_le.mp hp
  · intro h x hx
    rw [mem_primewisePadicIdealOfExponents] at hx ⊢
    intro p
    apply (show liftedPadicIdealOfExponent p (e p) ≤
      liftedPadicIdealOfExponent p (d p) by
        simpa [liftedPadicIdealOfExponent] using h p)
    exact hx p

/-- The ideal carried by a closed additive subgroup of the primewise p-adic
ring. -/
noncomputable def primewisePadicClosedAddSubgroupIdeal
    (K : ClosedAddSubgroup primewisePadicRing.{u}) :
    Ideal primewisePadicRing.{u} :=
  K.toAddSubgroup.toIdealOfIsClosedOfDenseIntCast K.isClosed'
    denseRange_intCast_primewisePadicRing

/-- The coordinatewise exponents of a closed additive subgroup of the
primewise p-adic ring. -/
noncomputable def primewisePadicClosedAddSubgroupExponents
    (K : ClosedAddSubgroup primewisePadicRing.{u}) : Nat.Primes → ℕ∞ :=
  primewisePadicIdealExponents (primewisePadicClosedAddSubgroupIdeal K)

/-- The closed additive subgroup having the prescribed primewise exponents. -/
noncomputable def primewisePadicClosedAddSubgroupOfExponents
    (e : Nat.Primes → ℕ∞) : ClosedAddSubgroup primewisePadicRing.{u} where
  toAddSubgroup := (primewisePadicIdealOfExponents e).toAddSubgroup
  isClosed' := isClosed_primewisePadicIdealOfExponents e

/-- Membership in the closed additive subgroup with prescribed exponents is
coordinatewise membership in the corresponding p-adic ideals. -/
@[simp]
theorem mem_primewisePadicClosedAddSubgroupOfExponents
    (e : Nat.Primes → ℕ∞) (x : primewisePadicRing.{u}) :
    x ∈ primewisePadicClosedAddSubgroupOfExponents e ↔
      ∀ p, x p ∈ liftedPadicIdealOfExponent p (e p) :=
  Iff.rfl

/-- A closed additive subgroup is reconstructed from its primewise
exponents. -/
@[simp]
theorem primewisePadicClosedAddSubgroupOfExponents_exponents
    (K : ClosedAddSubgroup primewisePadicRing.{u}) :
    primewisePadicClosedAddSubgroupOfExponents
      (primewisePadicClosedAddSubgroupExponents K) = K := by
  apply ClosedAddSubgroup.toAddSubgroup_injective
  have hCarrier :
      (primewisePadicClosedAddSubgroupIdeal K).toAddSubgroup =
        K.toAddSubgroup := by
    ext x
    rfl
  rw [← hCarrier]
  apply AddSubgroup.ext
  intro x
  exact SetLike.ext_iff.mp (eq_primewisePadicIdealOfExponents
    (primewisePadicClosedAddSubgroupIdeal K) K.isClosed').symm x

/-- Extracting exponents from the closed additive subgroup constructed from
them recovers the original family. -/
@[simp]
theorem primewisePadicClosedAddSubgroupExponents_ofExponents
    (e : Nat.Primes → ℕ∞) :
    primewisePadicClosedAddSubgroupExponents
      (primewisePadicClosedAddSubgroupOfExponents.{u} e) = e := by
  rw [primewisePadicClosedAddSubgroupExponents]
  have hIdeal : primewisePadicClosedAddSubgroupIdeal
      (primewisePadicClosedAddSubgroupOfExponents.{u} e) =
      primewisePadicIdealOfExponents e := by
    ext x
    rfl
  rw [hIdeal]
  exact primewisePadicIdealExponents_idealOfExponents e

/-- Primewise exponents uniquely determine a closed additive subgroup. -/
theorem primewisePadicClosedAddSubgroupOfExponents_injective :
    Function.Injective
      (primewisePadicClosedAddSubgroupOfExponents.{u} :
        (Nat.Primes → ℕ∞) → ClosedAddSubgroup primewisePadicRing.{u}) := by
  intro e d h
  simpa using congrArg primewisePadicClosedAddSubgroupExponents h

/-- Equality of closed additive subgroups constructed from exponents is
exactly equality of their exponent families. -/
@[simp]
theorem primewisePadicClosedAddSubgroupOfExponents_inj
    {e d : Nat.Primes → ℕ∞} :
    primewisePadicClosedAddSubgroupOfExponents.{u} e =
        primewisePadicClosedAddSubgroupOfExponents d ↔ e = d :=
  primewisePadicClosedAddSubgroupOfExponents_injective.eq_iff

/-- The inclusion order on closed additive subgroups is the reverse
pointwise order on exponent families. -/
@[simp]
theorem primewisePadicClosedAddSubgroupOfExponents_le_iff
    {e d : Nat.Primes → ℕ∞} :
    primewisePadicClosedAddSubgroupOfExponents.{u} e ≤
        primewisePadicClosedAddSubgroupOfExponents d ↔
      ∀ p, d p ≤ e p :=
  primewisePadicIdealOfExponents_le_iff

/-- Closed additive subgroups of the primewise p-adic ring, ordered by
inclusion, correspond to exponent families with the pointwise order
reversed. -/
noncomputable def primewisePadicClosedAddSubgroupOrderIso :
    ClosedAddSubgroup primewisePadicRing.{u} ≃o
      (Nat.Primes → ℕ∞)ᵒᵈ where
  toFun K := OrderDual.toDual (primewisePadicClosedAddSubgroupExponents K)
  invFun e := primewisePadicClosedAddSubgroupOfExponents (OrderDual.ofDual e)
  left_inv := primewisePadicClosedAddSubgroupOfExponents_exponents
  right_inv e := by simp
  map_rel_iff' := by
    intro K L
    constructor
    · intro h
      change ∀ p, primewisePadicClosedAddSubgroupExponents L p ≤
        primewisePadicClosedAddSubgroupExponents K p at h
      rw [← primewisePadicClosedAddSubgroupOfExponents_exponents K,
        ← primewisePadicClosedAddSubgroupOfExponents_exponents L]
      exact primewisePadicClosedAddSubgroupOfExponents_le_iff.mpr h
    · intro h
      change ∀ p, primewisePadicClosedAddSubgroupExponents L p ≤
        primewisePadicClosedAddSubgroupExponents K p
      rw [← primewisePadicClosedAddSubgroupOfExponents_exponents K,
        ← primewisePadicClosedAddSubgroupOfExponents_exponents L] at h
      exact primewisePadicClosedAddSubgroupOfExponents_le_iff.mp h

/-- Exponent zero gives the whole underlying additive subgroup. -/
@[simp]
theorem primewisePadicClosedAddSubgroupOfExponents_zero_toAddSubgroup :
    (primewisePadicClosedAddSubgroupOfExponents.{u} 0).toAddSubgroup = ⊤ := by
  change (primewisePadicIdealOfExponents 0).toAddSubgroup = ⊤
  rw [primewisePadicIdealOfExponents_zero]
  rfl

/-- Infinite exponent at every prime gives the trivial underlying additive
subgroup. -/
@[simp]
theorem primewisePadicClosedAddSubgroupOfExponents_top_toAddSubgroup :
    (primewisePadicClosedAddSubgroupOfExponents.{u} ⊤).toAddSubgroup = ⊥ := by
  change (primewisePadicIdealOfExponents ⊤).toAddSubgroup = ⊥
  rw [primewisePadicIdealOfExponents_top]
  rfl

/-- Transport a closed additive subgroup of the underlying ring to a closed
multiplicative subgroup of `primewisePadic`. -/
noncomputable def primewisePadicClosedAddSubgroupToClosedSubgroup
    (K : ClosedAddSubgroup primewisePadicRing.{u}) :
    ClosedSubgroup primewisePadic.{u} where
  toSubgroup := K.toAddSubgroup.toSubgroup.map
    primewisePadicRingMultiplicativeEquiv.toMulEquiv.toMonoidHom
  isClosed' := by
    change IsClosed (primewisePadicRingMultiplicativeEquiv.{u} ''
      (K : Set primewisePadicRing.{u}))
    exact primewisePadicRingMultiplicativeEquiv.toHomeomorph.isClosedMap _
      K.isClosed'

/-- Pull a closed subgroup of `primewisePadic` back to a closed additive
subgroup of its underlying product ring. -/
noncomputable def primewisePadicClosedSubgroupToClosedAddSubgroup
    (H : ClosedSubgroup primewisePadic.{u}) :
    ClosedAddSubgroup primewisePadicRing.{u} where
  toAddSubgroup := (H.toSubgroup.comap
    primewisePadicRingMultiplicativeEquiv.toMulEquiv.toMonoidHom).toAddSubgroup'
  isClosed' := by
    change IsClosed ((fun x : primewisePadicRing.{u} ↦
      primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) ⁻¹'
        (H : Set primewisePadic.{u}))
    exact H.isClosed'.preimage
      (primewisePadicRingMultiplicativeEquiv.continuous_toFun.comp
        continuous_ofAdd)

/-- Transporting a closed additive subgroup to `primewisePadic` and back is
the identity. -/
@[simp]
theorem primewisePadicClosedSubgroupToClosedAddSubgroup_toClosedSubgroup
    (K : ClosedAddSubgroup primewisePadicRing.{u}) :
    primewisePadicClosedSubgroupToClosedAddSubgroup
      (primewisePadicClosedAddSubgroupToClosedSubgroup K) = K := by
  apply ClosedAddSubgroup.toAddSubgroup_injective
  change Subgroup.toAddSubgroup'
      (Subgroup.comap _ (Subgroup.map _ K.toAddSubgroup.toSubgroup)) = _
  rw [Subgroup.comap_map_eq_self]
  · rfl
  · rw [MonoidHom.ker_eq_bot
      primewisePadicRingMultiplicativeEquiv.toMulEquiv.toMonoidHom
      primewisePadicRingMultiplicativeEquiv.injective]
    exact bot_le

/-- Pulling back a closed subgroup of `primewisePadic` and transporting it
forward is the identity. -/
@[simp]
theorem primewisePadicClosedAddSubgroupToClosedSubgroup_toClosedAddSubgroup
    (H : ClosedSubgroup primewisePadic.{u}) :
    primewisePadicClosedAddSubgroupToClosedSubgroup
      (primewisePadicClosedSubgroupToClosedAddSubgroup H) = H := by
  apply ClosedSubgroup.toSubgroup_injective
  change Subgroup.map _ (Subgroup.comap _ H.toSubgroup) = _
  apply Subgroup.map_comap_eq_self
  intro x _
  exact ⟨primewisePadicRingMultiplicativeEquiv.symm x,
    primewisePadicRingMultiplicativeEquiv.apply_symm_apply x⟩

/-- The continuous multiplicative equivalence identifies closed additive
subgroups of the underlying ring with closed subgroups of
`primewisePadic`, preserving inclusion. -/
noncomputable def primewisePadicClosedAddSubgroupClosedSubgroupOrderIso :
    ClosedAddSubgroup primewisePadicRing.{u} ≃o
      ClosedSubgroup primewisePadic.{u} where
  toFun := primewisePadicClosedAddSubgroupToClosedSubgroup
  invFun := primewisePadicClosedSubgroupToClosedAddSubgroup
  left_inv := primewisePadicClosedSubgroupToClosedAddSubgroup_toClosedSubgroup
  right_inv := primewisePadicClosedAddSubgroupToClosedSubgroup_toClosedAddSubgroup
  map_rel_iff' := by
    intro K L
    change Subgroup.map _ K.toAddSubgroup.toSubgroup ≤
      Subgroup.map _ L.toAddSubgroup.toSubgroup ↔ K ≤ L
    rw [Subgroup.map_le_map_iff]
    rw [MonoidHom.ker_eq_bot
      primewisePadicRingMultiplicativeEquiv.toMulEquiv.toMonoidHom
      primewisePadicRingMultiplicativeEquiv.injective]
    simp only [sup_bot_eq]
    rfl

/-- The closed subgroup of `primewisePadic` having the prescribed additive
coordinate exponents. -/
noncomputable def primewisePadicClosedSubgroupOfExponents
    (e : Nat.Primes → ℕ∞) : ClosedSubgroup primewisePadic.{u} :=
  primewisePadicClosedAddSubgroupToClosedSubgroup
    (primewisePadicClosedAddSubgroupOfExponents e)

/-- The additive coordinate exponents of a closed subgroup of
`primewisePadic`. -/
noncomputable def primewisePadicClosedSubgroupExponents
    (H : ClosedSubgroup primewisePadic.{u}) : Nat.Primes → ℕ∞ :=
  primewisePadicClosedAddSubgroupExponents
    (primewisePadicClosedSubgroupToClosedAddSubgroup H)

/-- Membership in a closed subgroup with prescribed exponents is tested on
the additive coordinates obtained from the inverse continuous equivalence. -/
@[simp]
theorem mem_primewisePadicClosedSubgroupOfExponents
    (e : Nat.Primes → ℕ∞) (x : primewisePadic.{u}) :
    x ∈ primewisePadicClosedSubgroupOfExponents e ↔
      ∀ p, (primewisePadicRingMultiplicativeEquiv.{u}.symm x).toAdd p ∈
        liftedPadicIdealOfExponent p (e p) := by
  change x ∈ Subgroup.map
      primewisePadicRingMultiplicativeEquiv.toMulEquiv.toMonoidHom
      (primewisePadicClosedAddSubgroupOfExponents e).toAddSubgroup.toSubgroup ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have heq : primewisePadicRingMultiplicativeEquiv.symm
        (primewisePadicRingMultiplicativeEquiv.toMulEquiv.toMonoidHom y) = y :=
      primewisePadicRingMultiplicativeEquiv.symm_apply_apply y
    rw [heq]
    exact (mem_primewisePadicClosedAddSubgroupOfExponents e y.toAdd).mp hy
  · intro hx
    refine ⟨primewisePadicRingMultiplicativeEquiv.symm x, ?_,
      primewisePadicRingMultiplicativeEquiv.apply_symm_apply x⟩
    exact (mem_primewisePadicClosedAddSubgroupOfExponents e _).mpr hx

/-- A closed subgroup of `primewisePadic` is reconstructed from its
coordinate exponents. -/
@[simp]
theorem primewisePadicClosedSubgroupOfExponents_exponents
    (H : ClosedSubgroup primewisePadic.{u}) :
    primewisePadicClosedSubgroupOfExponents
      (primewisePadicClosedSubgroupExponents H) = H := by
  rw [primewisePadicClosedSubgroupOfExponents,
    primewisePadicClosedSubgroupExponents,
    primewisePadicClosedAddSubgroupOfExponents_exponents,
    primewisePadicClosedAddSubgroupToClosedSubgroup_toClosedAddSubgroup]

/-- Extracting exponents from a closed subgroup constructed from them
recovers the original family. -/
@[simp]
theorem primewisePadicClosedSubgroupExponents_ofExponents
    (e : Nat.Primes → ℕ∞) :
    primewisePadicClosedSubgroupExponents
      (primewisePadicClosedSubgroupOfExponents.{u} e) = e := by
  rw [primewisePadicClosedSubgroupExponents,
    primewisePadicClosedSubgroupOfExponents,
    primewisePadicClosedSubgroupToClosedAddSubgroup_toClosedSubgroup,
    primewisePadicClosedAddSubgroupExponents_ofExponents]

/-- Closed subgroups of `primewisePadic`, ordered by inclusion, correspond
to additive coordinate exponent families with the pointwise order reversed.

Uses Mathlib’s closed-subgroup and p-adic ideal APIs and the local
`PrimewisePadicIdeals` correspondence; the full factor-ideal classification is not
stated as a book theorem. -/
noncomputable def primewisePadicClosedSubgroupOrderIso :
    ClosedSubgroup primewisePadic.{u} ≃o (Nat.Primes → ℕ∞)ᵒᵈ :=
  primewisePadicClosedAddSubgroupClosedSubgroupOrderIso.symm.trans
    primewisePadicClosedAddSubgroupOrderIso

/-- The inclusion order on closed multiplicative subgroups is the reverse
pointwise order on exponent families. -/
@[simp]
theorem primewisePadicClosedSubgroupOfExponents_le_iff
    {e d : Nat.Primes → ℕ∞} :
    primewisePadicClosedSubgroupOfExponents.{u} e ≤
        primewisePadicClosedSubgroupOfExponents d ↔
      ∀ p, d p ≤ e p := by
  change primewisePadicClosedAddSubgroupToClosedSubgroup
      (primewisePadicClosedAddSubgroupOfExponents e) ≤
    primewisePadicClosedAddSubgroupToClosedSubgroup
      (primewisePadicClosedAddSubgroupOfExponents d) ↔ _
  change primewisePadicClosedAddSubgroupClosedSubgroupOrderIso
      (primewisePadicClosedAddSubgroupOfExponents e) ≤
    primewisePadicClosedAddSubgroupClosedSubgroupOrderIso
      (primewisePadicClosedAddSubgroupOfExponents d) ↔ _
  rw [OrderIso.le_iff_le,
    primewisePadicClosedAddSubgroupOfExponents_le_iff]

/-- Primewise exponents uniquely determine a closed subgroup of
`primewisePadic`. -/
@[simp]
theorem primewisePadicClosedSubgroupOfExponents_inj
    {e d : Nat.Primes → ℕ∞} :
    primewisePadicClosedSubgroupOfExponents.{u} e =
        primewisePadicClosedSubgroupOfExponents d ↔ e = d := by
  constructor
  · intro h
    simpa using congrArg primewisePadicClosedSubgroupExponents h
  · exact congrArg primewisePadicClosedSubgroupOfExponents

/-- Exponent zero gives the whole underlying multiplicative subgroup. -/
@[simp]
theorem primewisePadicClosedSubgroupOfExponents_zero_toSubgroup :
    (primewisePadicClosedSubgroupOfExponents.{u} 0).toSubgroup = ⊤ := by
  ext x
  change x ∈ primewisePadicClosedSubgroupOfExponents 0 ↔ x ∈ (⊤ : Subgroup _)
  rw [mem_primewisePadicClosedSubgroupOfExponents]
  simp

/-- Infinite exponent at every prime gives the trivial underlying
multiplicative subgroup. -/
@[simp]
theorem primewisePadicClosedSubgroupOfExponents_top_toSubgroup :
    (primewisePadicClosedSubgroupOfExponents.{u} ⊤).toSubgroup = ⊥ := by
  ext x
  change x ∈ primewisePadicClosedSubgroupOfExponents ⊤ ↔ x ∈ (⊥ : Subgroup _)
  simp only [Subgroup.mem_bot, mem_primewisePadicClosedSubgroupOfExponents,
    Pi.top_apply, liftedPadicIdealOfExponent_top, Ideal.mem_bot]
  constructor
  · intro hx
    apply primewisePadicRingMultiplicativeEquiv.symm.injective
    apply Multiplicative.toAdd.injective
    exact funext hx
  · rintro rfl p
    rfl

/-- The primewise exponents of the kernel of a continuous multiplicative
homomorphism.  The target needs only a group, a topology, and the T1 axiom
used to make the kernel closed. -/
noncomputable def primewisePadicKernelExponents
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) : Nat.Primes → ℕ∞ :=
  primewisePadicIdealExponents (primewisePadicKernelIdeal f)

/-- The closed kernel ideal is reconstructed from its primewise exponents. -/
theorem primewisePadicKernelIdeal_eq_idealOfExponents
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) :
    primewisePadicKernelIdeal f =
      primewisePadicIdealOfExponents (primewisePadicKernelExponents f) :=
  eq_primewisePadicIdealOfExponents _ (isClosed_primewisePadicKernelIdeal f)

/-- An element is killed by a continuous homomorphism exactly when each of
its additive coordinates belongs to the p-adic ideal specified by the kernel
exponent. -/
theorem primewisePadic_map_eq_one_iff
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (x : primewisePadic.{u}) :
    f x = 1 ↔
      ∀ p, (primewisePadicRingMultiplicativeEquiv.{u}.symm x).toAdd p ∈
        liftedPadicIdealOfExponent p (primewisePadicKernelExponents f p) := by
  let a : primewisePadicRing.{u} :=
    (primewisePadicRingMultiplicativeEquiv.symm x).toAdd
  have hKernel : f x = 1 ↔ a ∈ primewisePadicKernelIdeal f := by
    simp [a]
  rw [hKernel, primewisePadicKernelIdeal_eq_idealOfExponents,
    mem_primewisePadicIdealOfExponents]

private theorem primewisePadicKernelIdeal_eq_bot_iff
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) :
    primewisePadicKernelIdeal f = ⊥ ↔ Function.Injective f := by
  constructor
  · intro hIdeal
    apply (MonoidHom.ker_eq_bot_iff f.toMonoidHom).mp
    ext x
    let a : primewisePadicRing.{u} :=
      (primewisePadicRingMultiplicativeEquiv.symm x).toAdd
    simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
    have hKernel : f x = 1 ↔ a ∈ primewisePadicKernelIdeal f := by
      simp [a]
    change f x = 1 ↔ x = 1
    rw [hKernel, hIdeal, Ideal.mem_bot]
    constructor
    · intro ha
      apply primewisePadicRingMultiplicativeEquiv.symm.injective
      apply Multiplicative.toAdd.injective
      simpa [a] using ha
    · rintro rfl
      rfl
  · intro hf
    ext a
    rw [Ideal.mem_bot, mem_primewisePadicKernelIdeal]
    constructor
    · intro ha
      apply Multiplicative.ofAdd.injective
      apply primewisePadicRingMultiplicativeEquiv.injective
      apply hf
      simpa using ha
    · rintro rfl
      simp

private theorem primewisePadicKernelIdeal_eq_top_iff
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) :
    primewisePadicKernelIdeal f = ⊤ ↔ f = 1 := by
  constructor
  · intro hIdeal
    apply ContinuousMonoidHom.ext
    intro x
    let a : primewisePadicRing.{u} :=
      (primewisePadicRingMultiplicativeEquiv.symm x).toAdd
    have ha : a ∈ primewisePadicKernelIdeal f := by
      rw [hIdeal]
      exact Submodule.mem_top
    have hfa := (mem_primewisePadicKernelIdeal f a).mp ha
    simpa [a] using hfa
  · rintro rfl
    ext a
    simp

/-- A continuous homomorphism from `primewisePadic` is injective exactly when
every kernel exponent is infinite. -/
theorem primewisePadic_injective_iff_kernelExponents_eq_top
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) :
    Function.Injective f ↔ ∀ p, primewisePadicKernelExponents f p = ⊤ := by
  rw [← primewisePadicKernelIdeal_eq_bot_iff f]
  constructor
  · intro h p
    have hExponents : primewisePadicKernelExponents f = ⊤ :=
      primewisePadicIdealOfExponents_injective (by
        rw [← primewisePadicKernelIdeal_eq_idealOfExponents, h,
          primewisePadicIdealOfExponents_top])
    exact congrFun hExponents p
  · intro h
    rw [primewisePadicKernelIdeal_eq_idealOfExponents]
    rw [show primewisePadicKernelExponents f = ⊤ by
      funext p
      exact h p]
    exact primewisePadicIdealOfExponents_top

/-- A continuous homomorphism from `primewisePadic` is trivial exactly when
every kernel exponent is zero. -/
theorem primewisePadic_eq_one_iff_kernelExponents_eq_zero
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) :
    f = 1 ↔ ∀ p, primewisePadicKernelExponents f p = 0 := by
  rw [← primewisePadicKernelIdeal_eq_top_iff f]
  constructor
  · intro h p
    have hExponents : primewisePadicKernelExponents f = 0 :=
      primewisePadicIdealOfExponents_injective (by
        rw [← primewisePadicKernelIdeal_eq_idealOfExponents, h,
          primewisePadicIdealOfExponents_zero])
    exact congrFun hExponents p
  · intro h
    rw [primewisePadicKernelIdeal_eq_idealOfExponents]
    rw [show primewisePadicKernelExponents f = 0 by
      funext p
      exact h p]
    exact primewisePadicIdealOfExponents_zero

end ProfiniteGrp
