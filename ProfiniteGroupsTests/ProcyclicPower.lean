/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicPower

/-!
# Procyclic power-image clients

Check power images, positive-index divisibility, quotient generators, and open
subgroup classification through the public power API.
-/

@[expose] public section

open ProfiniteGrp

set_option linter.style.haveILetI false

universe u

namespace ProcyclicPowerTest

theorem power_hom_application (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (n : ℕ) (x : G) :
    powerHom G hG n x = x ^ n := powerHom_apply G hG n x

theorem proof_parameter_independence (G : ProfiniteGrp.{u})
    (hG kG : IsProcyclic G) (n : ℕ) :
    powerHom G hG n = powerHom G kG n ∧
      powerImage G hG n = powerImage G kG n := ⟨rfl, rfl⟩

theorem zero_and_one (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) :
    (powerImage G hG 0 : Subgroup G) = ⊥ ∧
      (powerImage G hG 1 : Subgroup G) = ⊤ :=
  ⟨powerImage_zero G hG, powerImage_one G hG⟩

theorem open_and_divides (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (n : ℕ) (hn : 0 < n) :
    IsOpen ((powerImage G hG n : Subgroup G) : Set G) ∧
      (powerImage G hG n : Subgroup G).index ∣ n :=
  ⟨powerImage_isOpen G hG n hn, powerImage_index_dvd G hG n hn⟩

theorem subgroup_generator (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (g : G)
    (hg : IsTopologicalGenerator G g) (n : ℕ) :
    (powerImage G hG n : Subgroup G) =
        (Subgroup.zpowers (g ^ n)).topologicalClosure ∧
      IsTopologicalGenerator (ofClosedSubgroup (powerImage G hG n))
        (powerHomToImage G hG n g) :=
  ⟨powerImage_eq_topologicalClosure_zpowers G hG g hg n,
   powerHomToImage_isTopologicalGenerator G hG g hg n⟩

theorem quotient_generator (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (g : G)
    (hg : IsTopologicalGenerator G g) (n : ℕ) (hn : 0 < n) :
    IsCyclic (G ⧸ (powerImage G hG n : Subgroup G)) ∧
      Finite (G ⧸ (powerImage G hG n : Subgroup G)) ∧
      Subgroup.zpowers ((QuotientGroup.mk' (powerImage G hG n : Subgroup G)) g) = ⊤ :=
  ⟨powerImage_quotient_isCyclic G hG g hg n hn,
   powerImage_quotient_finite G hG n hn,
   powerImage_quotient_zpowers_eq_top G hG g hg n hn⟩

theorem all_open (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (H : OpenSubgroup G) :
    (H : Subgroup G) = (powerImage G hG (H : Subgroup G).index : Subgroup G) :=
  openSubgroup_eq_powerImage G hG H

theorem subgroup_bridge (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (H : Subgroup G)
    (hH : IsOpen (H : Set G)) : H = (powerImage G hG H.index : Subgroup G) :=
  subgroup_eq_powerImage_of_isOpen G hG H hH

theorem equal_index_unique (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (H K : OpenSubgroup G) (hidx : (H : Subgroup G).index = (K : Subgroup G).index) :
    H = K := openSubgroup_eq_of_index_eq G hG H K hidx

theorem open_membership (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) (n : ℕ)
    (hn : 0 < n) (x : G) (hx : x ∈ powerOpenSubgroup G hG n hn) :
    ∃ y : G, y ^ n = x :=
  (mem_powerImage_iff G hG n x).mp hx

private theorem c2_pow_four (x : finiteCyclic 2) : x ^ 4 = 1 := by
  change Multiplicative (ZMod 2) at x
  apply Multiplicative.toAdd.injective
  change (4 : ℕ) • (x.toAdd : ZMod 2) = 0
  rw [nsmul_eq_mul]
  simp [show (4 : ZMod 2) = 0 by decide]

private theorem c4_gen_not_square :
    (finiteCyclicGenerator 4 : finiteCyclic 4) ∉
      powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 := by
  rw [mem_powerImage_iff]
  rintro ⟨y, hy⟩
  letI : Fintype (finiteCyclic 4) := by
    change Fintype (Multiplicative (ZMod 4))
    infer_instance
  change Multiplicative (ZMod 4) at y
  have heq := congrArg Multiplicative.toAdd hy
  change (2 : ℕ) • (y.toAdd : ZMod 4) = 1 at heq
  rw [nsmul_eq_mul] at heq
  change (2 : ZMod 4) * (show Multiplicative (ZMod 4) from y).toAdd = 1 at heq
  fin_cases y
  all_goals first
    | change (2 : ZMod 4) * 0 = 1 at heq
    | change (2 : ZMod 4) * 1 = 1 at heq
  all_goals norm_num at heq
  all_goals first
    | exact (by decide : (0 : ZMod 4) ≠ 1) heq
    | exact (by decide : (2 : ZMod 4) ≠ 1) heq

private theorem c3_square_surjective (x : finiteCyclic 3) :
    x ∈ powerImage (finiteCyclic 3) (finiteCyclic_isProcyclic 3) 2 := by
  rw [mem_powerImage_iff]
  have hc3 : x ^ 3 = 1 := by
    change Multiplicative (ZMod 3) at x
    apply Multiplicative.toAdd.injective
    change (3 : ℕ) • (x.toAdd : ZMod 3) = 0
    rw [nsmul_eq_mul]
    simp [show (3 : ZMod 3) = 0 by decide]
  refine ⟨x ^ 2, ?_⟩
  calc
    (x ^ 2) ^ 2 = x ^ (2 * 2) := (pow_mul x 2 2).symm
    _ = x := by rw [show 2 * 2 = 3 + 1 by decide, pow_succ, hc3, one_mul]

theorem two_fourth_index : (powerImage (finiteCyclic 2) (finiteCyclic_isProcyclic 2) 4 :
    Subgroup (finiteCyclic 2)).index = 2 := by
  have hbot : (powerImage (finiteCyclic 2) (finiteCyclic_isProcyclic 2) 4 :
      Subgroup (finiteCyclic 2)) = ⊥ := by
    ext x
    change (∃ y : finiteCyclic 2, y ^ 4 = x) ↔ x = 1
    constructor
    · rintro ⟨y, rfl⟩
      exact c2_pow_four y
    · intro hx
      exact ⟨1, by simpa using hx.symm⟩
  rw [hbot, Subgroup.index_bot]
  change Nat.card (Multiplicative (ZMod 2)) = 2
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem three_square_index : (powerImage (finiteCyclic 3) (finiteCyclic_isProcyclic 3) 2 :
    Subgroup (finiteCyclic 3)).index = 1 := by
  have htop : (powerImage (finiteCyclic 3) (finiteCyclic_isProcyclic 3) 2 :
      Subgroup (finiteCyclic 3)) = ⊤ := by
    ext x
    exact ⟨fun _ => Subgroup.mem_top x, fun _ => c3_square_surjective x⟩
  rw [htop, Subgroup.index_top]

theorem four_square_index : (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 :
    Subgroup (finiteCyclic 4)).index = 2 := by
  have hdiv := powerImage_index_dvd (finiteCyclic 4) (finiteCyclic_isProcyclic 4)
    2 (by decide)
  have hpos : 0 < (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 :
      Subgroup (finiteCyclic 4)).index :=
    Nat.pos_of_ne_zero (powerImage_finiteIndex (finiteCyclic 4)
      (finiteCyclic_isProcyclic 4) 2 (by decide)).index_ne_zero
  have hne : (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 :
      Subgroup (finiteCyclic 4)).index ≠ 1 := by
    intro hidx
    have htop := Subgroup.index_eq_one.mp hidx
    have hg : finiteCyclicGenerator 4 ∈ powerImage (finiteCyclic 4)
        (finiteCyclic_isProcyclic 4) 2 := by
      change finiteCyclicGenerator 4 ∈
        (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 : Subgroup _)
      rw [htop]
      exact Subgroup.mem_top _
    exact c4_gen_not_square hg
  have hle : (powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 :
      Subgroup (finiteCyclic 4)).index ≤ 2 := Nat.le_of_dvd (by decide) hdiv
  omega

theorem four_square_nontrivial : ∃ x : finiteCyclic 4,
    x ∈ powerImage (finiteCyclic 4) (finiteCyclic_isProcyclic 4) 2 ∧ x ≠ 1 := by
  refine ⟨(finiteCyclicGenerator 4)^2,
    (mem_powerImage_iff _ _ _ _).mpr ⟨finiteCyclicGenerator 4, rfl⟩, ?_⟩
  change (2 : ℕ) • (1 : ZMod 4) ≠ 0
  decide

theorem trivial_power_top : (powerImage (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))
    ProfiniteGrp.punit_isProcyclic 7 :
    Subgroup (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit))) = ⊤ := by
  ext x
  change PUnit at x
  change (∃ y : PUnit, y ^ 7 = x) ↔ True
  exact ⟨fun _ => trivial, fun _ => ⟨PUnit.unit, Subsingleton.elim _ _⟩⟩

end ProcyclicPowerTest

end
