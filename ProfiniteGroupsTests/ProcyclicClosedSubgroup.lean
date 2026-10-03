/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicClosedSubgroup
public import ProfiniteGroups.ProcyclicPower

/-!
# Closed procyclic subgroup clients

Test inheritance and generator construction for arbitrary closed subgroups,
including a proper non-open subgroup of an infinite primewise product.
-/

@[expose] public section

open ProfiniteGrp

universe u

namespace ProcyclicClosedSubgroupTest

theorem bottom_case (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) :
    IsProcyclic (ProfiniteGrp.ofClosedSubgroup
      (⟨(⊥ : Subgroup G), by
        change IsClosed ({(1 : G)} : Set G)
        exact isClosed_singleton⟩ : ClosedSubgroup G)) :=
  hG.ofClosedSubgroup ⟨⊥, by
    change IsClosed ({(1 : G)} : Set G)
    exact isClosed_singleton⟩

theorem top_case (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) :
    IsProcyclic (ProfiniteGrp.ofClosedSubgroup
      (⟨(⊤ : Subgroup G), by
        change IsClosed (Set.univ : Set G)
        exact isClosed_univ⟩ : ClosedSubgroup G)) :=
  hG.ofClosedSubgroup ⟨⊤, by
    change IsClosed (Set.univ : Set G)
    exact isClosed_univ⟩

theorem trivial_case :
    IsProcyclic (ProfiniteGrp.ofClosedSubgroup
      (⟨(⊥ : Subgroup (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))),
        by
          change IsClosed
            ({(1 : ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))} : Set _)
          exact isClosed_singleton⟩ :
        ClosedSubgroup (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit)))) :=
  punit_isProcyclic.ofClosedSubgroup ⟨⊥, by
    change IsClosed
      ({(1 : ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))} : Set _)
    exact isClosed_singleton⟩

private theorem c4_generator_not_square :
    (finiteCyclicGenerator 4 : finiteCyclic 4) ∉
      powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 := by
  rw [mem_powerImage_iff]
  rintro ⟨y, hy⟩
  change Multiplicative (ZMod 4) at y
  have heq := congrArg Multiplicative.toAdd hy
  change (2 : ℕ) • (y.toAdd : ZMod 4) = 1 at heq
  rw [nsmul_eq_mul] at heq
  change (2 : ZMod 4) * (show Multiplicative (ZMod 4) from y).toAdd = 1 at heq
  let : Fintype (finiteCyclic 4) := by
    change Fintype (Multiplicative (ZMod 4))
    infer_instance
  fin_cases y
  all_goals first
    | change (2 : ZMod 4) * 0 = 1 at heq
    | change (2 : ZMod 4) * 1 = 1 at heq
  all_goals norm_num at heq
  all_goals first
    | exact (by decide : (0 : ZMod 4) ≠ 1) heq
    | exact (by decide : (2 : ZMod 4) ≠ 1) heq

theorem c4_proper_nontrivial_subgroup :
    (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 :
      Subgroup (finiteCyclic 4)) ≠ ⊤ ∧
    (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 :
      Subgroup (finiteCyclic 4)) ≠ ⊥ := by
  constructor
  · intro htop
    apply c4_generator_not_square
    change finiteCyclicGenerator 4 ∈
      (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 : Subgroup _)
    rw [htop]
    trivial
  · intro hbot
    have hmem : (finiteCyclicGenerator 4)^2 ∈
        powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 :=
      (mem_powerImage_iff _ _ _ _).mpr ⟨finiteCyclicGenerator 4, rfl⟩
    change (finiteCyclicGenerator 4)^2 ∈
      (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 : Subgroup _) at hmem
    rw [hbot] at hmem
    have heq : (finiteCyclicGenerator 4)^2 = 1 :=
      (Subgroup.mem_bot).mp hmem
    change (2 : ℕ) • (1 : ZMod 4) = 0 at heq
    exact (by decide : (2 : ℕ) • (1 : ZMod 4) ≠ 0) heq

theorem c4_proper_nontrivial_isProcyclic :
    IsProcyclic (ProfiniteGrp.ofClosedSubgroup
      (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2)) := by
  let H : Subgroup (finiteCyclic 4) :=
    powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2
  have hH : IsClosed (H : Set (finiteCyclic 4)) :=
    (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2).isClosed'
  exact (finiteCyclic_isProcyclic 4).ofSubgroup_isClosed H hH

def zeroAtTwo (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then ⊤ else 0

noncomputable def twoZeroSubgroup : ClosedSubgroup primewisePadic.{0} :=
  primewisePadicClosedSubgroupOfExponents zeroAtTwo

theorem primewise_twoZero_nontrivial :
    (twoZeroSubgroup : Subgroup primewisePadic.{0}) ≠ ⊥ := by
  let three : Nat.Primes := ⟨3, by decide⟩
  let coordinate : primewisePadicRing.{0} := Pi.single three 1
  let element : primewisePadic.{0} := primewisePadicRingMultiplicativeEquiv
    (Multiplicative.ofAdd coordinate)
  have hmem : element ∈ twoZeroSubgroup := by
    apply (mem_primewisePadicClosedSubgroupOfExponents zeroAtTwo element).mpr
    intro p
    change coordinate p ∈
      liftedPadicIdealOfExponent p (zeroAtTwo p)
    by_cases hp : p.1 = 2
    · have hne : p ≠ three := by
        intro heq
        have h := congrArg Subtype.val heq
        change p.1 = 3 at h
        omega
      simp [coordinate, zeroAtTwo, hp, hne]
    · simp [zeroAtTwo, hp]
  have hne : element ≠ 1 := by
    intro heq
    have h := congrArg
      (fun x : primewisePadic.{0} ↦
        (primewisePadicRingMultiplicativeEquiv.symm x).toAdd three) heq
    change coordinate three = 0 at h
    simp [coordinate] at h
  intro hbot
  have hunit : element = 1 := (Subgroup.mem_bot).mp (hbot ▸ hmem)
  exact hne hunit

theorem primewise_twoZero_proper :
    (twoZeroSubgroup : Subgroup primewisePadic.{0}) ≠ ⊤ := by
  intro htop
  have hmem : primewisePadicGenerator.{0} ∈ twoZeroSubgroup := by
    change primewisePadicGenerator.{0} ∈ (twoZeroSubgroup : Subgroup _)
    rw [htop]
    trivial
  let two : Nat.Primes := ⟨2, by decide⟩
  have hcoord := (mem_primewisePadicClosedSubgroupOfExponents
    zeroAtTwo primewisePadicGenerator.{0}).mp hmem two
  have htwo : zeroAtTwo two = ⊤ := by simp [zeroAtTwo, two]
  rw [htwo, liftedPadicIdealOfExponent_top] at hcoord
  change (ULift.up (1 : ℤ_[2])) ∈ (⊥ : Ideal (ULift.{0} ℤ_[2])) at hcoord
  have hzero : (ULift.up (1 : ℤ_[2])) = 0 :=
    (Submodule.mem_bot (ULift.{0} ℤ_[2])).mp hcoord
  exact one_ne_zero (congrArg ULift.down hzero)

theorem primewise_twoZero_not_open :
    ¬ IsOpen (twoZeroSubgroup : Set primewisePadic.{0}) := by
  intro hOpen
  have : Finite (primewisePadic.{0} ⧸ (twoZeroSubgroup : Subgroup _)) :=
    Subgroup.quotient_finite_of_isOpen _ hOpen
  have : (twoZeroSubgroup : Subgroup primewisePadic.{0}).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  let n := (twoZeroSubgroup : Subgroup primewisePadic.{0}).index
  have hn : 0 < n := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have heq := openSubgroup_eq_powerImage primewisePadic.{0}
    primewisePadic_isProcyclic ⟨(twoZeroSubgroup : Subgroup _), hOpen⟩
  change (twoZeroSubgroup : Subgroup primewisePadic.{0}) =
    (powerImage primewisePadic.{0} primewisePadic_isProcyclic n : Subgroup _) at heq
  have hpow : (primewisePadicGenerator.{0} ^ n) ∈ twoZeroSubgroup := by
    change (primewisePadicGenerator.{0} ^ n) ∈ (twoZeroSubgroup : Subgroup _)
    rw [heq]
    exact (mem_powerImage_iff _ _ _ _).mpr ⟨primewisePadicGenerator, rfl⟩
  let two : Nat.Primes := ⟨2, by decide⟩
  have hmem := (mem_primewisePadicClosedSubgroupOfExponents
    zeroAtTwo (primewisePadicGenerator.{0} ^ n)).mp hpow two
  change ((primewisePadicGenerator.{0} ^ n) two).toAdd ∈
    liftedPadicIdealOfExponent two (zeroAtTwo two) at hmem
  have htwo : zeroAtTwo two = ⊤ := by simp [zeroAtTwo, two]
  rw [htwo, liftedPadicIdealOfExponent_top] at hmem
  rw [← zpow_natCast, primewisePadicGenerator_zpow] at hmem
  change (ULift.up (n : ℤ_[2])) ∈ (⊥ : Ideal (ULift.{0} ℤ_[2])) at hmem
  have hzero : (ULift.up (n : ℤ_[2])) = 0 :=
    (Submodule.mem_bot (ULift.{0} ℤ_[2])).mp hmem
  have hcast : (n : ℤ_[2]) = 0 := congrArg ULift.down hzero
  exact (Nat.ne_of_gt hn) (by exact_mod_cast hcast)

theorem primewise_isInfinite : Infinite primewisePadic.{0} := by
  by_contra hInfinite
  have : Finite primewisePadic.{0} := not_infinite_iff_finite.mp hInfinite
  exact primewise_twoZero_not_open (isOpen_discrete _)

theorem primewise_twoZero_closed_nonOpen_isProcyclic :
    IsProcyclic (ProfiniteGrp.ofClosedSubgroup twoZeroSubgroup) ∧
      ¬ IsOpen (twoZeroSubgroup : Set primewisePadic.{0}) ∧
      (twoZeroSubgroup : Subgroup primewisePadic.{0}) ≠ ⊥ ∧
      (twoZeroSubgroup : Subgroup primewisePadic.{0}) ≠ ⊤ :=
  ⟨primewisePadic_isProcyclic.ofClosedSubgroup twoZeroSubgroup,
    primewise_twoZero_not_open, primewise_twoZero_nontrivial,
    primewise_twoZero_proper⟩

end ProcyclicClosedSubgroupTest
