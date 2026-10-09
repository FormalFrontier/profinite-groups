/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ContinuousSection
public import Mathlib.Topology.Homeomorph.Quotient

/-!
# Continuous representatives of closed cosets

Every closed subgroup `H` of a profinite group `G` admits a chosen continuous
representative map from `G ⧸ H` to `G`. Its composite with the coset projection
is the identity, even when `H` is not normal.

The choice is not asserted to preserve multiplication, fix the identity,
commute with conjugation, or be natural in the subgroup. The quotient by the
bottom subgroup is identified with `G` using Mathlib's quotient-by-bottom
homeomorphism and a change of quotient relation.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, Exercise 4
  (through the continuous section theorem in `ProfiniteGroups.ContinuousSection`).
- Mathlib, `Mathlib.Topology.Homeomorph.Quotient` and
  `Mathlib.Topology.Algebra.Group.Quotient` (the quotient topology and the
  quotient-by-bottom homeomorphism).
-/

@[expose] public section

universe u

namespace Subgroup

private def quotientBotHomeomorph {G : Type u} [Group G] [TopologicalSpace G] :
    G ⧸ (⊥ : Subgroup G) ≃ₜ G :=
  (Homeomorph.Quotient.congrRight
    (r := QuotientGroup.leftRel (⊥ : Subgroup G)) (r' := ⊥)
    (fun x y ↦ by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_bot, inv_mul_eq_one]
      change x = y ↔ x = y
      rfl))
      |>.trans Homeomorph.quotientBot

private theorem quotientBotHomeomorph_apply_mk {G : Type u} [Group G]
    [TopologicalSpace G] (g : G) :
    quotientBotHomeomorph (QuotientGroup.mk g : G ⧸ (⊥ : Subgroup G)) = g := by
  rfl

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Every closed subgroup of a profinite group admits a bundled continuous
choice of coset representatives. The proof specializes the closed-coset
section theorem at the bottom subgroup. -/
theorem exists_continuous_coset_representative (H : Subgroup G)
    [IsClosed (H : Set G)] :
    ∃ s : C(G ⧸ H, G), ∀ q, QuotientGroup.mk (s q) = q := by
  let _ : IsClosed ((⊥ : Subgroup G) : Set G) := ⟨by simp⟩
  obtain ⟨s, hs, hright⟩ :=
    quotientMapOfLE_exists_continuous_section_of_isClosed
      (K := (⊥ : Subgroup G)) (H := H) bot_le
  refine ⟨⟨quotientBotHomeomorph ∘ s,
    quotientBotHomeomorph.continuous.comp hs⟩, ?_⟩
  intro q
  have hprojection (x : G ⧸ (⊥ : Subgroup G)) :
      QuotientGroup.mk (quotientBotHomeomorph x) =
        quotientMapOfLE (bot_le : (⊥ : Subgroup G) ≤ H) x := by
    induction x using Quotient.inductionOn with
    | _ g =>
      simp only [quotientBotHomeomorph_apply_mk, quotientMapOfLE_apply_mk]
  exact (hprojection (s q)).trans (hright q)

/-- A continuous choice of representatives for the left cosets of a closed
subgroup of a profinite group. This choice need not be a homomorphism or
send the identity coset to the identity. -/
noncomputable def continuousCosetRepresentative (H : Subgroup G)
    [IsClosed (H : Set G)] : C(G ⧸ H, G) :=
  (exists_continuous_coset_representative H).choose

/-- The chosen representative lies in its specified coset. -/
@[simp]
theorem continuousCosetRepresentative_mk (H : Subgroup G)
    [IsClosed (H : Set G)] (q : G ⧸ H) :
    QuotientGroup.mk (H.continuousCosetRepresentative q) = q :=
  (exists_continuous_coset_representative H).choose_spec q

/-- Choosing a representative is a right inverse of the coset projection. -/
theorem continuousCosetRepresentative_rightInverse (H : Subgroup G)
    [IsClosed (H : Set G)] :
    Function.RightInverse H.continuousCosetRepresentative
      (QuotientGroup.mk : G → G ⧸ H) :=
  H.continuousCosetRepresentative_mk

/-- Representatives of distinct cosets are distinct. -/
theorem continuousCosetRepresentative_injective (H : Subgroup G)
    [IsClosed (H : Set G)] : Function.Injective H.continuousCosetRepresentative := by
  intro q r h
  calc
    q = QuotientGroup.mk (H.continuousCosetRepresentative q) :=
      (H.continuousCosetRepresentative_mk q).symm
    _ = QuotientGroup.mk (H.continuousCosetRepresentative r) := congrArg _ h
    _ = r := H.continuousCosetRepresentative_mk r

end Subgroup
