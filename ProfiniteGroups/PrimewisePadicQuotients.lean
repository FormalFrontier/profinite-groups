/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.PiIdealQuotient
public import ProfiniteGroups.PrimewisePadicIdeals
public import Mathlib.Topology.Algebra.Ring.Compact

/-!
# Quotient models for primewise p-adic ideals

This file identifies a finite-exponent uplifted p-adic quotient with the
corresponding residue ring, an infinite-exponent quotient with the p-adic
factor itself, and packages both cases in a universe-polymorphic profinite
additive factor.  Taking products gives a model for arbitrary mixtures of
zero, positive finite, and infinite primewise exponents.

The zero exponent quotient is trivial; a finite positive exponent gives a
residue factor; the infinite exponent gives the full p-adic factor.
-/

@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Reduction modulo `p ^ n` on an uplifted p-adic factor. -/
noncomputable def liftedPadicToZModPow (p : Nat.Primes) (n : ℕ) :
    ULift.{u} ℤ_[p.1] →+* ZMod (p.1 ^ n) :=
  (PadicInt.toZModPow n).comp ULift.ringEquiv.toRingHom

/-- Uplifted p-adic reduction acts by lowering the lift and reducing. -/
@[simp]
theorem liftedPadicToZModPow_apply (p : Nat.Primes) (n : ℕ)
    (x : ULift.{u} ℤ_[p.1]) :
    liftedPadicToZModPow p n x = PadicInt.toZModPow n x.down :=
  rfl

/-- Uplifted reduction modulo `p ^ n` is surjective. -/
theorem liftedPadicToZModPow_surjective (p : Nat.Primes) (n : ℕ) :
    Function.Surjective (liftedPadicToZModPow.{u} p n) := by
  exact ZMod.ringHom_surjective _

/-- The kernel of uplifted reduction modulo `p ^ n` is the ideal with finite
exponent `n`. -/
theorem ker_liftedPadicToZModPow (p : Nat.Primes) (n : ℕ) :
    RingHom.ker (liftedPadicToZModPow.{u} p n) =
      liftedPadicIdealOfExponent p (n : ℕ∞) := by
  rw [liftedPadicIdealOfExponent_natCast, PadicInt.maximalIdeal_eq_span_p,
    Ideal.span_singleton_pow]
  ext x
  change PadicInt.toZModPow n x.down = 0 ↔
    x.down ∈ Ideal.span {(p.1 : ℤ_[p.1]) ^ n}
  rw [← PadicInt.ker_toZModPow]
  exact RingHom.mem_ker.symm

/-- A finite-exponent uplifted p-adic quotient is the expected residue ring.
This includes `n = 0`, where the target is `ZMod 1`. -/
noncomputable def liftedPadicQuotientRingEquivZMod (p : Nat.Primes) (n : ℕ) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p (n : ℕ∞)) ≃+*
      ZMod (p.1 ^ n) :=
  (Ideal.quotEquivOfEq (ker_liftedPadicToZModPow p n).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := liftedPadicToZModPow p n)
      (liftedPadicToZModPow_surjective p n))

/-- The finite quotient equivalence is induced by p-adic reduction. -/
@[simp]
theorem liftedPadicQuotientRingEquivZMod_mk (p : Nat.Primes) (n : ℕ)
    (x : ULift.{u} ℤ_[p.1]) :
    liftedPadicQuotientRingEquivZMod p n
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p (n : ℕ∞)) x) =
      PadicInt.toZModPow n x.down := by
  simp only [liftedPadicQuotientRingEquivZMod, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk,
    liftedPadicToZModPow_apply]

/-- A finite-exponent ideal in an uplifted p-adic factor is open. -/
theorem isOpen_liftedPadicIdealOfExponent_natCast
    (p : Nat.Primes) (n : ℕ) :
    IsOpen ((liftedPadicIdealOfExponent p (n : ℕ∞) :
      Ideal (ULift.{u} ℤ_[p.1])) : Set (ULift.{u} ℤ_[p.1])) := by
  rw [liftedPadicIdealOfExponent_natCast]
  change IsOpen (Homeomorph.ulift ⁻¹'
    ((IsLocalRing.maximalIdeal ℤ_[p.1] ^ n : Ideal ℤ_[p.1]) : Set ℤ_[p.1]))
  exact (Homeomorph.ulift (X := ℤ_[p.1])).isOpen_preimage.mpr
    (IsLocalRing.isOpen_maximalIdeal_pow ℤ_[p.1] n)

/-- The topology on a finite-exponent uplifted p-adic quotient is discrete.
The proof uses openness of the source ideal, rather than only discreteness of
the target residue ring. -/
theorem discreteTopology_liftedPadicQuotient_natCast
    (p : Nat.Primes) (n : ℕ) :
    DiscreteTopology
      (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p (n : ℕ∞)) :=
  QuotientAddGroup.discreteTopology
    (isOpen_liftedPadicIdealOfExponent_natCast p n)

/-- The finite residue-ring equivalence as a continuous additive equivalence. -/
noncomputable def liftedPadicQuotientContinuousAddEquivZMod
    (p : Nat.Primes) (n : ℕ) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p (n : ℕ∞)) ≃ₜ+
      ZMod (p.1 ^ n) := by
  letI := discreteTopology_liftedPadicQuotient_natCast.{u} p n
  exact ContinuousAddEquiv.mk
    (liftedPadicQuotientRingEquivZMod p n).toAddEquiv
      continuous_of_discreteTopology continuous_of_discreteTopology

/-- The continuous finite quotient equivalence is coherent with the ring
equivalence. -/
@[simp]
theorem liftedPadicQuotientContinuousAddEquivZMod_apply
    (p : Nat.Primes) (n : ℕ)
    (x : ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p (n : ℕ∞)) :
    liftedPadicQuotientContinuousAddEquivZMod p n x =
      liftedPadicQuotientRingEquivZMod p n x :=
  rfl

/-- The zero-exponent factor is the quotient by the unit ideal and is
canonically continuously equivalent to `ZMod 1`. -/
noncomputable def liftedPadicQuotientContinuousAddEquivZero
    (p : Nat.Primes) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p 0) ≃ₜ+ ZMod 1 := by
  rw [← ENat.natCast_zero]
  have h := liftedPadicQuotientContinuousAddEquivZMod.{u} p 0
  rw [pow_zero] at h
  exact h

/-- The infinite-exponent quotient ring is the uplifted p-adic ring itself. -/
noncomputable def liftedPadicQuotientRingEquivTop (p : Nat.Primes) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p ⊤) ≃+*
      ULift.{u} ℤ_[p.1] :=
  (Ideal.quotEquivOfEq (liftedPadicIdealOfExponent_top p)).trans
    (RingEquiv.quotientBot _)

/-- The infinite-exponent ring equivalence sends a quotient representative to
that representative. -/
@[simp]
theorem liftedPadicQuotientRingEquivTop_mk (p : Nat.Primes)
    (x : ULift.{u} ℤ_[p.1]) :
    liftedPadicQuotientRingEquivTop p
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p ⊤) x) = x := by
  rfl

/-- The infinite-exponent quotient is continuously additively equivalent to
the uplifted p-adic factor. -/
noncomputable def liftedPadicQuotientContinuousAddEquivTop
    (p : Nat.Primes) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p ⊤) ≃ₜ+
      ULift.{u} ℤ_[p.1] :=
  ContinuousAddEquiv.mk (liftedPadicQuotientRingEquivTop p).toAddEquiv
    (by
      rw [← (QuotientRing.isOpenQuotientMap_mk
        (liftedPadicIdealOfExponent p ⊤)).continuous_comp_iff]
      change Continuous (id : ULift.{u} ℤ_[p.1] → ULift.{u} ℤ_[p.1])
      exact continuous_id)
    (by
      change Continuous (Ideal.Quotient.mk
        (liftedPadicIdealOfExponent p ⊤))
      exact (QuotientRing.isOpenQuotientMap_mk _).continuous)

/-- The continuous infinite quotient equivalence is coherent with the ring
equivalence. -/
@[simp]
theorem liftedPadicQuotientContinuousAddEquivTop_apply
    (p : Nat.Primes)
    (x : ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p ⊤) :
    liftedPadicQuotientContinuousAddEquivTop p x =
      liftedPadicQuotientRingEquivTop p x :=
  rfl

/-- The infinite p-adic branch, bundled as a profinite additive group in the
chosen universe. -/
noncomputable def padicQuotientFactorTop (p : Nat.Primes) :
    ProfiniteAddGrp.{u} := by
  letI : CompactSpace (ULift.{u} ℤ_[p.1]) :=
    Homeomorph.compactSpace (Homeomorph.ulift (X := ℤ_[p.1])).symm
  letI : TotallyDisconnectedSpace (ULift.{u} ℤ_[p.1]) :=
    Homeomorph.totallyDisconnectedSpace
      (Homeomorph.ulift (X := ℤ_[p.1])).symm
  exact ProfiniteAddGrp.of (ULift.{u} ℤ_[p.1])

/-- The finite residue branch, bundled as a profinite additive group in the
chosen universe. -/
noncomputable def padicQuotientFactorNat (p : Nat.Primes) (n : ℕ) :
    ProfiniteAddGrp.{u} := by
  letI : CompactSpace (ULift.{u} (ZMod (p.1 ^ n))) :=
    Homeomorph.compactSpace
      (Homeomorph.ulift (X := ZMod (p.1 ^ n))).symm
  letI : TotallyDisconnectedSpace (ULift.{u} (ZMod (p.1 ^ n))) :=
    Homeomorph.totallyDisconnectedSpace
      (Homeomorph.ulift (X := ZMod (p.1 ^ n))).symm
  exact ProfiniteAddGrp.of (ULift.{u} (ZMod (p.1 ^ n)))

/-- The universe-uniform factor model: an infinite exponent gives an uplifted
p-adic factor, and a finite exponent `n` gives an uplifted `ZMod (p ^ n)`.
The use of `ENat.recTopCoe` keeps the two cases explicit. -/
noncomputable def padicQuotientFactor (p : Nat.Primes) (e : ℕ∞) :
    ProfiniteAddGrp.{u} :=
  ENat.recTopCoe (padicQuotientFactorTop p)
    (padicQuotientFactorNat p) e

/-- The infinite branch equation for the universe-uniform factor model. -/
@[simp]
theorem padicQuotientFactor_top (p : Nat.Primes) :
    padicQuotientFactor.{u} p ⊤ = padicQuotientFactorTop p :=
  ENat.recTopCoe_top _ _

/-- The finite branch equation for the universe-uniform factor model. -/
@[simp]
theorem padicQuotientFactor_natCast (p : Nat.Primes) (n : ℕ) :
    padicQuotientFactor.{u} p (n : ℕ∞) = padicQuotientFactorNat p n :=
  ENat.recTopCoe_natCast _ _ _

/-- The additive homeomorphism from a finite residue ring to its universe
lift. -/
noncomputable def zmodContinuousAddEquivULift (p : Nat.Primes) (n : ℕ) :
    ZMod (p.1 ^ n) ≃ₜ+ ULift.{u} (ZMod (p.1 ^ n)) :=
  ContinuousAddEquiv.mk ULift.ringEquiv.symm.toAddEquiv
    continuous_of_discreteTopology continuous_of_discreteTopology

/-- A quotient factor is continuously additively equivalent to its
universe-uniform finite-or-infinite model. -/
noncomputable def liftedPadicQuotientContinuousAddEquivFactor
    (p : Nat.Primes) (e : ℕ∞) :
    (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p e) ≃ₜ+
      padicQuotientFactor p e := by
  refine ENat.recTopCoe ?_ (fun n ↦ ?_) e
  · change (ULift.{u} ℤ_[p.1] ⧸ liftedPadicIdealOfExponent p ⊤) ≃ₜ+
      ULift.{u} ℤ_[p.1]
    exact liftedPadicQuotientContinuousAddEquivTop.{u} p
  · change (ULift.{u} ℤ_[p.1] ⧸
        liftedPadicIdealOfExponent p (n : ℕ∞)) ≃ₜ+
      ULift.{u} (ZMod (p.1 ^ n))
    exact (liftedPadicQuotientContinuousAddEquivZMod.{u} p n).trans
      (zmodContinuousAddEquivULift.{u} p n)

/-- In the infinite branch, the factor equivalence sends a quotient
representative to that representative. -/
@[simp]
theorem liftedPadicQuotientContinuousAddEquivFactor_top_mk
    (p : Nat.Primes) (x : ULift.{u} ℤ_[p.1]) :
    liftedPadicQuotientContinuousAddEquivFactor p ⊤
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p ⊤) x) = x := by
  change liftedPadicQuotientContinuousAddEquivTop p
      (Ideal.Quotient.mk (liftedPadicIdealOfExponent p ⊤) x) = x
  exact liftedPadicQuotientRingEquivTop_mk p x

/-- In a finite branch, the factor equivalence reduces modulo `p ^ n` and
then lifts the result to the chosen universe. -/
@[simp]
theorem liftedPadicQuotientContinuousAddEquivFactor_natCast_mk
    (p : Nat.Primes) (n : ℕ) (x : ULift.{u} ℤ_[p.1]) :
    liftedPadicQuotientContinuousAddEquivFactor p (n : ℕ∞)
        (Ideal.Quotient.mk
          (liftedPadicIdealOfExponent p (n : ℕ∞)) x) =
      ULift.up (PadicInt.toZModPow n x.down) := by
  change zmodContinuousAddEquivULift p n
      (liftedPadicQuotientContinuousAddEquivZMod p n
        (Ideal.Quotient.mk
          (liftedPadicIdealOfExponent p (n : ℕ∞)) x)) = _
  rw [liftedPadicQuotientContinuousAddEquivZMod_apply,
    liftedPadicQuotientRingEquivZMod_mk]
  rfl

/-- The product of the universe-uniform coordinate factor models. -/
noncomputable def primewisePadicQuotientModel
    (e : Nat.Primes → ℕ∞) : ProfiniteAddGrp.{u} :=
  ProfiniteAddGrp.pi fun p ↦ padicQuotientFactor p (e p)

/-- The product of a dependent family of continuous additive equivalences. -/
noncomputable def continuousAddEquivPiCongrRight
    {ι : Type*} {A B : ι → Type*}
    [∀ i, Add (A i)] [∀ i, Add (B i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    (F : ∀ i, A i ≃ₜ+ B i) : (∀ i, A i) ≃ₜ+ (∀ i, B i) :=
  ContinuousAddEquiv.mk (AddEquiv.piCongrRight fun i ↦ (F i).toAddEquiv)
    (Homeomorph.piCongrRight (fun i ↦ (F i).toHomeomorph)).continuous
    (Homeomorph.piCongrRight (fun i ↦ (F i).toHomeomorph)).symm.continuous

/-- The product equivalence acts coordinatewise. -/
@[simp]
theorem continuousAddEquivPiCongrRight_apply
    {ι : Type*} {A B : ι → Type*}
    [∀ i, Add (A i)] [∀ i, Add (B i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]
    (F : ∀ i, A i ≃ₜ+ B i) (x : ∀ i, A i) (i : ι) :
    continuousAddEquivPiCongrRight F x i = F i (x i) :=
  rfl

/-- Split a dependent additive product into the coordinates satisfying a
predicate and those satisfying its negation. -/
noncomputable def continuousAddEquivPiSubtypeProd
    {ι : Type*} (P : ι → Prop) (F : ι → Type*)
    [∀ i, Add (F i)] [∀ i, TopologicalSpace (F i)] :
    (∀ i, F i) ≃ₜ+ (∀ i : {i // P i}, F i) × (∀ i : {i // ¬ P i}, F i) := by
  classical
  exact ContinuousAddEquiv.mk
    { toEquiv := Equiv.piEquivPiSubtypeProd P F
      map_add' := fun _ _ ↦ rfl }
    (Homeomorph.piEquivPiSubtypeProd P F).continuous
    (Homeomorph.piEquivPiSubtypeProd P F).symm.continuous

/-- Forgetting addition recovers the usual equivalence of dependent products. -/
theorem continuousAddEquivPiSubtypeProd_toEquiv
    {ι : Type*} (P : ι → Prop) (F : ι → Type*)
    [∀ i, Add (F i)] [∀ i, TopologicalSpace (F i)] [DecidablePred P] :
    (continuousAddEquivPiSubtypeProd P F).toEquiv =
      Equiv.piEquivPiSubtypeProd P F := by
  apply Equiv.ext
  intro x
  rfl

/-- The first half of a split product retains the coordinates in the predicate. -/
@[simp]
theorem continuousAddEquivPiSubtypeProd_apply_fst
    {ι : Type*} (P : ι → Prop) (F : ι → Type*)
    [∀ i, Add (F i)] [∀ i, TopologicalSpace (F i)]
    (x : ∀ i, F i) (i : {i // P i}) :
    (continuousAddEquivPiSubtypeProd P F x).1 i = x i.1 := by
  classical
  rfl

/-- The second half of a split product retains the complementary coordinates. -/
@[simp]
theorem continuousAddEquivPiSubtypeProd_apply_snd
    {ι : Type*} (P : ι → Prop) (F : ι → Type*)
    [∀ i, Add (F i)] [∀ i, TopologicalSpace (F i)]
    (x : ∀ i, F i) (i : {i // ¬ P i}) :
    (continuousAddEquivPiSubtypeProd P F x).2 i = x i.1 := by
  classical
  rfl

/-- Remove coordinates that are subsingletons from a dependent additive
product. The removed coordinates need not form a finite set. -/
noncomputable def continuousAddEquivPiSubtype
    {ι : Type*} (P : ι → Prop) (F : ι → Type*)
    [∀ i, AddMonoid (F i)] [∀ i, TopologicalSpace (F i)]
    [∀ i : {i // ¬ P i}, Subsingleton (F i.1)] :
    (∀ i, F i) ≃ₜ+ (∀ i : {i // P i}, F i) := by
  letI : Unique (∀ i : {i // ¬ P i}, F i.1) :=
    { default := fun _ ↦ 0
      uniq := fun _ ↦ funext fun _ ↦ Subsingleton.elim _ _ }
  let drop : ((∀ i : {i // P i}, F i.1) ×
      (∀ i : {i // ¬ P i}, F i.1)) ≃ₜ+ (∀ i : {i // P i}, F i.1) :=
    ContinuousAddEquiv.mk AddEquiv.prodUnique
      (Homeomorph.prodUnique _ _).continuous
      (Homeomorph.prodUnique _ _).symm.continuous
  exact (continuousAddEquivPiSubtypeProd P F).trans drop

/-- The retained coordinates of the subtype-product equivalence are unchanged. -/
@[simp]
theorem continuousAddEquivPiSubtype_apply
    {ι : Type*} (P : ι → Prop) (F : ι → Type*)
    [∀ i, AddMonoid (F i)] [∀ i, TopologicalSpace (F i)]
    [∀ i : {i // ¬ P i}, Subsingleton (F i.1)]
    (x : ∀ i, F i) (i : {i // P i}) :
    continuousAddEquivPiSubtype P F x i = x i.1 :=
  rfl

/-- The quotient by an arbitrary primewise exponent ideal is continuously
additively equivalent, in the forward quotient-to-model direction, to the
complete product of its finite and infinite factor models. -/
noncomputable def primewisePadicQuotientContinuousAddEquivModel
    (e : Nat.Primes → ℕ∞) :
    (primewisePadicRing.{u} ⧸ primewisePadicIdealOfExponents e) ≃ₜ+
      primewisePadicQuotientModel e :=
  (Ideal.piQuotientContinuousAddEquiv
    (fun p ↦ liftedPadicIdealOfExponent p (e p))).trans
      (continuousAddEquivPiCongrRight fun p ↦
        liftedPadicQuotientContinuousAddEquivFactor p (e p))

/-- On a quotient representative, the mixed primewise model equivalence
reduces the selected coordinate and then applies its finite-or-infinite factor
equivalence. -/
@[simp]
theorem primewisePadicQuotientContinuousAddEquivModel_mk_apply
    (e : Nat.Primes → ℕ∞) (x : primewisePadicRing.{u})
    (p : Nat.Primes) :
    primewisePadicQuotientContinuousAddEquivModel e
        (Ideal.Quotient.mk (primewisePadicIdealOfExponents e) x) p =
      liftedPadicQuotientContinuousAddEquivFactor p (e p)
        (Ideal.Quotient.mk (liftedPadicIdealOfExponent p (e p)) (x p)) := by
  rfl

end ProfiniteGrp
