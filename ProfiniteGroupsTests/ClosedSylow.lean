/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProfiniteGroups.ClosedSylow
public import Mathlib.Algebra.Group.PUnit

/-!
# Clients for closed subgroups with Sylow finite-quotient images

Tests bounded maximality and prescribed finite-quotient images, including the
trivial profinite group. These examples use Mathlib's `PUnit` and `Sylow` APIs.
-/

public section

set_option warningAsError true

universe u

example (G : ProfiniteGrp.{u}) (p : ℕ) (hp : p.Prime)
    (s : G.CompatibleSylowFamily p hp) (H : Subgroup G)
    (hPH : s.closedSubgroup.toSubgroup ≤ H)
    (hH : ∀ U : OpenNormalSubgroup G,
      IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup))) :
    H = s.closedSubgroup.toSubgroup := by
  exact ProfiniteGrp.eq_closedSylow_of_le_of_isPGroup_images s.closedSubgroup
    (fun U => ⟨s.at U, s.map_closedSubgroup U⟩) H hPH hH

example (p : ℕ) (hp : p.Prime)
    (U : OpenNormalSubgroup (ProfiniteGrp.of PUnit)) :
    ∃ P : ClosedSubgroup (ProfiniteGrp.of PUnit),
      P.toSubgroup = ⊤ ∧
        P.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) =
          (Sylow.nonempty.some : Sylow p
            ((ProfiniteGrp.of PUnit) ⧸ U.toSubgroup)) := by
  let Q : Sylow p ((ProfiniteGrp.of PUnit) ⧸ U.toSubgroup) :=
    Sylow.nonempty.some
  obtain ⟨P, hPQ, _⟩ :=
    (ProfiniteGrp.of PUnit).exists_closedSylow_with p hp U Q
  refine ⟨P, ?_, ?_⟩
  · apply SetLike.ext
    intro x
    have hx : x = 1 := Subsingleton.elim x 1
    subst x
    simp
  · exact hPQ
