/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicPowerIndices
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Final

/-!
# Inverse systems of procyclic power quotients

Positive integers supported on a set of primes index the quotients by power
images. An arrow from `n` to `d` means `d ∣ n`, so the quotient map goes from
the finer `n`-th-power quotient to the coarser `d`-th-power quotient. The
finite-quotient functor and canonical cone are restrictions of Mathlib's
open-normal-subgroup constructions.

Every open normal subgroup of a procyclic group is a power image at its
index. Thus the all-positive power indices form an initial subdiagram of the
open normal subgroups. For a torsion-free procyclic group, these indices are
supported on the infinite-exponent primes, so the supported subdiagram is
also initial. Reindexing Mathlib's open-normal limit cone gives both
reconstruction results.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Nat

/-- A positive exponent supported on `S`. Its order is *reverse* divisibility:
`n ≤ d` means `d ∣ n`, the direction of the quotient transition. -/
@[ext]
structure PowerIndex (S : Set Nat.Primes) where
  /-- The underlying positive natural exponent. -/
  val : ℕ
  /-- The permitted prime factors of the exponent. -/
  property : val ∈ primeSupportedIndices S

namespace PowerIndex

variable {S : Set Nat.Primes}

/-- Every power index is strictly positive, including at full support. -/
theorem pos (n : PowerIndex S) : 0 < n.val :=
  (mem_primeSupportedIndices_iff.mp n.property).1

/-- Reverse divisibility makes supported exponents a category of quotient levels. -/
instance : PartialOrder (PowerIndex S) where
  le n d := d.val ∣ n.val
  le_refl n := dvd_refl n.val
  le_trans _ _ _ hnm hmd := dvd_trans hmd hnm
  le_antisymm n d hnd hdn := by
    apply PowerIndex.ext
    exact Nat.dvd_antisymm hdn hnd

/-- The inequality `n ≤ d` is exactly the divisibility `d ∣ n`. -/
theorem le_iff (n d : PowerIndex S) : n ≤ d ↔ d.val ∣ n.val := Iff.rfl

/-- A morphism from `n` to `d` witnesses `d ∣ n`. -/
theorem dvd_of_hom {n d : PowerIndex S} (f : n ⟶ d) : d.val ∣ n.val :=
  (le_iff n d).mp f.le

/-- The level `1` is terminal for every prime support. -/
instance : OrderTop (PowerIndex S) where
  top := ⟨1, (primeSupportedIndices S).one_mem⟩
  le_top n := Nat.one_dvd n.val

@[simp] theorem top_val : (⊤ : PowerIndex S).val = 1 := rfl

/-- Multiplication provides a common finer quotient level. -/
instance : Mul (PowerIndex S) where
  mul n d := ⟨n.val * d.val, (primeSupportedIndices S).mul_mem n.property d.property⟩

@[simp] theorem mul_val (n d : PowerIndex S) : (n * d).val = n.val * d.val := rfl

/-- Multiplying levels refines the first factor. -/
theorem mul_le_left (n d : PowerIndex S) : n * d ≤ n := by
  exact ⟨d.val, rfl⟩

/-- Multiplying levels refines the second factor. -/
theorem mul_le_right (n d : PowerIndex S) : n * d ≤ d := by
  exact ⟨n.val, by simp only [mul_val, mul_comm]⟩

/-- Any two power levels have a common refinement under reverse divisibility. -/
instance : IsCodirectedOrder (PowerIndex S) where
  directed n d := ⟨n * d, mul_le_left n d, mul_le_right n d⟩

instance : Nonempty (PowerIndex S) := ⟨⊤⟩

/-- An exponent in the existing prime-supported submonoid gives a power level. -/
def ofSupported (n : ℕ) (hn : n ∈ primeSupportedIndices S) : PowerIndex S :=
  ⟨n, hn⟩

@[simp] theorem ofSupported_val (n : ℕ) (hn : n ∈ primeSupportedIndices S) :
    (ofSupported n hn).val = n := rfl

/-- Every strictly positive exponent is a level at full support. -/
def ofPositive (n : ℕ) (hn : 0 < n) : PowerIndex (Set.univ : Set Nat.Primes) :=
  ⟨n, mem_primeSupportedIndices_univ.mpr hn⟩

@[simp] theorem ofPositive_val (n : ℕ) (hn : 0 < n) :
    (ofPositive n hn).val = n := rfl

/-- Empty prime support permits only level `1`. -/
theorem eq_top_of_empty (n : PowerIndex (∅ : Set Nat.Primes)) : n = ⊤ := by
  apply PowerIndex.ext
  exact (Submonoid.mem_bot.mp (by simpa using n.property))

end PowerIndex

end Nat

namespace ProfiniteGrp

/-- The open normal subgroup of `n`-th powers at a supported positive level. -/
def powerOpenNormalSubgroup (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    {S : Set Nat.Primes} (n : Nat.PowerIndex S) : OpenNormalSubgroup G := by
  letI : IsMulCommutative G := hG.isMulCommutative
  exact ⟨powerOpenSubgroup G hG n.val n.pos,
    Subgroup.normal_of_isMulCommutative _⟩

@[simp] theorem powerOpenNormalSubgroup_toSubgroup (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) {S : Set Nat.Primes} (n : Nat.PowerIndex S) :
    (powerOpenNormalSubgroup G hG n).toSubgroup =
      (powerImage G hG n.val : Subgroup G) := rfl

/-- The actual index of an open normal subgroup is a positive power level. -/
noncomputable def positivePowerIndexOfOpenNormal (G : ProfiniteGrp.{u})
    (U : OpenNormalSubgroup G) : Nat.PowerIndex (Set.univ : Set Nat.Primes) :=
  Nat.PowerIndex.ofPositive U.toSubgroup.index (by
    have hfinite : Finite (G ⧸ U.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
    exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_iff_finite.mpr hfinite))

@[simp] theorem positivePowerIndexOfOpenNormal_val (G : ProfiniteGrp.{u})
    (U : OpenNormalSubgroup G) : (positivePowerIndexOfOpenNormal G U).val =
      U.toSubgroup.index := rfl

/-- For a torsion-free procyclic group, the actual index of an open normal
subgroup is supported on the infinite-exponent primes. -/
noncomputable def supportedPowerIndexOfOpenNormal (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (hfree : IsMulTorsionFree G) (U : OpenNormalSubgroup G) :
    Nat.PowerIndex {p | hG.exponents p = ⊤} :=
  Nat.PowerIndex.ofSupported U.toSubgroup.index
    (openSubgroup_index_mem_primeSupportedIndices G hG hfree U.toOpenSubgroup)

@[simp] theorem supportedPowerIndexOfOpenNormal_val (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (hfree : IsMulTorsionFree G) (U : OpenNormalSubgroup G) :
    (supportedPowerIndexOfOpenNormal G hG hfree U).val = U.toSubgroup.index := rfl

/-- Every open normal quotient is a positive power quotient at its actual
index, including for procyclic groups with torsion. -/
theorem powerOpenNormalSubgroup_positive_index (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (U : OpenNormalSubgroup G) :
    powerOpenNormalSubgroup G hG (positivePowerIndexOfOpenNormal G U) = U := by
  apply OpenNormalSubgroup.toSubgroup_injective
  change (powerOpenNormalSubgroup G hG (positivePowerIndexOfOpenNormal G U)).toSubgroup =
    U.toSubgroup
  rw [powerOpenNormalSubgroup_toSubgroup, positivePowerIndexOfOpenNormal_val]
  exact (openSubgroup_eq_powerImage G hG U.toOpenSubgroup).symm

/-- Over the infinite-exponent support, every open normal quotient of a
torsion-free procyclic group again occurs at its actual power index. -/
theorem powerOpenNormalSubgroup_supported_index (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (hfree : IsMulTorsionFree G) (U : OpenNormalSubgroup G) :
    powerOpenNormalSubgroup G hG (supportedPowerIndexOfOpenNormal G hG hfree U) =
      U := by
  apply OpenNormalSubgroup.toSubgroup_injective
  change (powerOpenNormalSubgroup G hG
    (supportedPowerIndexOfOpenNormal G hG hfree U)).toSubgroup = U.toSubgroup
  rw [powerOpenNormalSubgroup_toSubgroup, supportedPowerIndexOfOpenNormal_val]
  exact (openSubgroup_eq_powerImage G hG U.toOpenSubgroup).symm

/-- Reverse-divisibility indexing of open normal power images. -/
def powerIndexFunctor (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (S : Set Nat.Primes) : Nat.PowerIndex S ⥤ OpenNormalSubgroup G :=
  (show Monotone (fun n : Nat.PowerIndex S => powerOpenNormalSubgroup G hG n) from
    fun n d hnd => by
      change (powerImage G hG n.val : Subgroup G) ≤
        (powerImage G hG d.val : Subgroup G)
      exact powerImage_le_of_dvd G hG ((Nat.PowerIndex.le_iff n d).mp hnd)).functor

@[simp] theorem powerIndexFunctor_obj (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes) (n : Nat.PowerIndex S) :
    (powerIndexFunctor G hG S).obj n = powerOpenNormalSubgroup G hG n := rfl

/-- The finite power-quotient functor, obtained by reindexing Mathlib's finite
open-normal quotient functor. -/
def powerQuotientFiniteFunctor (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (S : Set Nat.Primes) : Nat.PowerIndex S ⥤ FiniteGrp :=
  powerIndexFunctor G hG S ⋙ G.toFiniteQuotientFunctor

/-- The order of a finite power-quotient coordinate is its actual subgroup
index, which may be smaller than the exponent. -/
theorem powerQuotientFiniteFunctor_card (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes) (n : Nat.PowerIndex S) :
    Nat.card ((powerQuotientFiniteFunctor G hG S).obj n) =
      (powerImage G hG n.val : Subgroup G).index :=
  (powerImage G hG n.val : Subgroup G).index_eq_card.symm

/-- The corresponding diagram of profinite groups, with finite coordinates. -/
def powerQuotientDiagram (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (S : Set Nat.Primes) : Nat.PowerIndex S ⥤ ProfiniteGrp.{u} :=
  powerIndexFunctor G hG S ⋙ G.diagram

/-- The power-quotient cone consists of the canonical quotient projections. -/
def powerQuotientCone (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (S : Set Nat.Primes) : Cone (powerQuotientDiagram G hG S) :=
  G.cone.whisker (powerIndexFunctor G hG S)

/-- The quotient-class component of the canonical power-quotient cone. -/
@[simp] theorem powerQuotientCone_π_apply (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes) (n : Nat.PowerIndex S) (g : G) :
    (powerQuotientCone G hG S).π.app n g =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g := rfl

/-- Evaluation of a diagram transition on a quotient class. -/
@[simp] theorem powerQuotientDiagram_map_mk (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes) {n d : Nat.PowerIndex S}
    (f : n ⟶ d) (g : G) :
    (powerQuotientDiagram G hG S).map f
      (QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g) =
      QuotientGroup.mk' (powerImage G hG d.val : Subgroup G) g := by
  have h := congrArg (fun m : G ⟶ (powerQuotientDiagram G hG S).obj d => m g)
    ((powerQuotientCone G hG S).w f)
  change (powerQuotientDiagram G hG S).map f
      ((powerQuotientCone G hG S).π.app n g) =
      (powerQuotientCone G hG S).π.app d g at h
  simpa only [powerQuotientCone_π_apply] using h

/-- The reindexed Mathlib transition is the existing continuous power-quotient
map, not merely a map with the same source and target. -/
theorem powerQuotientDiagram_map_apply (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes) {n d : Nat.PowerIndex S}
    (f : n ⟶ d) (q : G ⧸ (powerImage G hG n.val : Subgroup G)) :
    (powerQuotientDiagram G hG S).map f q =
      powerImage_quotientMap G hG (Nat.PowerIndex.dvd_of_hom f) q := by
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (powerImage G hG n.val : Subgroup G) q
  rw [powerQuotientDiagram_map_mk, powerImage_quotientMap_apply_mk]

/-- The projection from the explicit profinite-group limit evaluates the
compatible family at its indicated power level. -/
@[simp] theorem powerQuotientLimit_π_apply (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes) (n : Nat.PowerIndex S)
    (x : ProfiniteGrp.limit (powerQuotientDiagram G hG S)) :
    (ProfiniteGrp.limitCone (powerQuotientDiagram G hG S)).π.app n x =
      x.val n := rfl

/-- The canonical homomorphism from a procyclic group into its power-quotient limit. -/
def toPowerQuotientLimit (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (S : Set Nat.Primes) : G ⟶ ProfiniteGrp.limit (powerQuotientDiagram G hG S) :=
  (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S)).lift
    (powerQuotientCone G hG S)

/-- Every coordinate of the canonical map is the corresponding quotient class. -/
@[simp] theorem toPowerQuotientLimit_apply (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes) (n : Nat.PowerIndex S) (g : G) :
    (toPowerQuotientLimit G hG S g).val n =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g := by
  have h := congrArg (fun f : G ⟶ (powerQuotientDiagram G hG S).obj n => f g)
    ((ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S)).fac
      (powerQuotientCone G hG S) n)
  change ((ProfiniteGrp.limitCone (powerQuotientDiagram G hG S)).π.app n)
      (toPowerQuotientLimit G hG S g) =
      (powerQuotientCone G hG S).π.app n g at h
  change (ProfiniteGrp.limitCone (powerQuotientDiagram G hG S)).π.app n
      (toPowerQuotientLimit G hG S g) =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g
  exact h.trans (powerQuotientCone_π_apply G hG S n g)

/-- If every open normal subgroup is represented by a supported power level,
the power levels form an initial subdiagram of the open normal quotients. -/
theorem powerIndexFunctor_initial_of_exists (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (S : Set Nat.Primes)
    (hcover : ∀ U : OpenNormalSubgroup G,
      ∃ n : Nat.PowerIndex S, powerOpenNormalSubgroup G hG n = U) :
    (powerIndexFunctor G hG S).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered (powerIndexFunctor G hG S)
  · intro U
    obtain ⟨n, hn⟩ := hcover U
    refine ⟨n, ⟨?_⟩⟩
    exact eqToHom (by simpa only [powerIndexFunctor_obj] using hn)
  · intro U n s s'
    exact ⟨n, 𝟙 n, Subsingleton.elim _ _⟩

/-- Every procyclic profinite group is the limit of its power quotients over
all positive integers, without a torsion-free hypothesis. -/
noncomputable def isLimit_powerQuotientCone (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) :
    IsLimit (powerQuotientCone G hG (Set.univ : Set Nat.Primes)) := by
  letI := powerIndexFunctor_initial_of_exists G hG (Set.univ : Set Nat.Primes)
    (fun U ↦ ⟨positivePowerIndexOfOpenNormal G U,
      powerOpenNormalSubgroup_positive_index G hG U⟩)
  exact (Functor.Initial.isLimitWhiskerEquiv (powerIndexFunctor G hG _) G.cone).symm
    G.isLimitCone

/-- Powers supported on the infinite-exponent primes recover a torsion-free
procyclic group. The support cannot in general replace all positive levels
in the presence of torsion. -/
noncomputable def isLimit_supportedPowerQuotientCone (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (hfree : IsMulTorsionFree G) :
    IsLimit (powerQuotientCone G hG {p | hG.exponents p = ⊤}) := by
  letI := powerIndexFunctor_initial_of_exists G hG {p | hG.exponents p = ⊤}
    (fun U ↦ ⟨supportedPowerIndexOfOpenNormal G hG hfree U,
      powerOpenNormalSubgroup_supported_index G hG hfree U⟩)
  exact (Functor.Initial.isLimitWhiskerEquiv (powerIndexFunctor G hG _) G.cone).symm
    G.isLimitCone

/-- Turn an IsLimit proof into a continuous group equivalence. The only
assumption here is the explicitly supplied limit certificate. -/
noncomputable def continuousMulEquivPowerQuotientLimitOfIsLimit
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (S : Set Nat.Primes)
    (hlimit : IsLimit (powerQuotientCone G hG S)) :
    G ≃ₜ* ProfiniteGrp.limit (powerQuotientDiagram G hG S) := by
  let iso := IsLimit.conePointUniqueUpToIso hlimit
    (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S))
  exact { CompHausLike.homeoOfIso ((forget₂ ProfiniteGrp Profinite).mapIso iso) with
    map_mul' := map_mul iso.hom.hom }

/-- The equivalence induced by an IsLimit certificate sends an element to
its compatible family of quotient classes. -/
@[simp] theorem continuousMulEquivPowerQuotientLimitOfIsLimit_apply
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (S : Set Nat.Primes)
    (hlimit : IsLimit (powerQuotientCone G hG S))
    (n : Nat.PowerIndex S) (g : G) :
    (continuousMulEquivPowerQuotientLimitOfIsLimit G hG S hlimit g).val n =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g := by
  have h := congrArg (fun f : G ⟶ (powerQuotientDiagram G hG S).obj n => f g)
    (IsLimit.conePointUniqueUpToIso_hom_comp hlimit
      (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S)) n)
  change ((ProfiniteGrp.limitCone (powerQuotientDiagram G hG S)).π.app n)
      ((IsLimit.conePointUniqueUpToIso hlimit
        (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S))).hom g) =
      (powerQuotientCone G hG S).π.app n g at h
  have hmap : continuousMulEquivPowerQuotientLimitOfIsLimit G hG S hlimit g =
      (IsLimit.conePointUniqueUpToIso hlimit
        (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S))).hom g := rfl
  rw [hmap]
  change (ProfiniteGrp.limitCone (powerQuotientDiagram G hG S)).π.app n
      ((IsLimit.conePointUniqueUpToIso hlimit
        (ProfiniteGrp.limitConeIsLimit (powerQuotientDiagram G hG S))).hom g) =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g
  exact h.trans (powerQuotientCone_π_apply G hG S n g)

/-- Continuous reconstruction over every positive exponent. -/
noncomputable def continuousMulEquivPowerQuotientLimit (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) :
    G ≃ₜ* ProfiniteGrp.limit (powerQuotientDiagram G hG (Set.univ : Set Nat.Primes)) :=
  continuousMulEquivPowerQuotientLimitOfIsLimit G hG _
    (isLimit_powerQuotientCone G hG)

/-- The all-positive equivalence sends an element to its power-quotient classes. -/
@[simp] theorem continuousMulEquivPowerQuotientLimit_apply
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (n : Nat.PowerIndex (Set.univ : Set Nat.Primes)) (g : G) :
    (continuousMulEquivPowerQuotientLimit G hG g).val n =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g :=
  continuousMulEquivPowerQuotientLimitOfIsLimit_apply G hG _ _ n g

/-- Continuous reconstruction at the infinite-exponent supported levels
of a torsion-free procyclic group. -/
noncomputable def continuousMulEquivSupportedPowerQuotientLimit
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (hfree : IsMulTorsionFree G) :
    G ≃ₜ* ProfiniteGrp.limit (powerQuotientDiagram G hG {p | hG.exponents p = ⊤}) :=
  continuousMulEquivPowerQuotientLimitOfIsLimit G hG _
    (isLimit_supportedPowerQuotientCone G hG hfree)

/-- The support-restricted equivalence sends an element to its
power-quotient classes. -/
@[simp] theorem continuousMulEquivSupportedPowerQuotientLimit_apply
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (hfree : IsMulTorsionFree G)
    (n : Nat.PowerIndex {p | hG.exponents p = ⊤}) (g : G) :
    (continuousMulEquivSupportedPowerQuotientLimit G hG hfree g).val n =
      QuotientGroup.mk' (powerImage G hG n.val : Subgroup G) g :=
  continuousMulEquivPowerQuotientLimitOfIsLimit_apply G hG _ _ n g

end ProfiniteGrp
