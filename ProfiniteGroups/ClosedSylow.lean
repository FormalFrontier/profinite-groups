/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProfiniteGroups.CompatibleSubgroups
public import ProfiniteGroups.CompatibleSylow

@[expose] public section

/-!
# Closed subgroups with Sylow finite-quotient images

A compatible choice of Sylow subgroups in every open-normal quotient reconstructs
a closed subgroup with exactly those images. Such a subgroup is maximal among
subgroups containing it whose images in every finite quotient are `p`-groups.
-/

namespace ProfiniteGrp

universe u

/-- Reconstruct a closed subgroup from compatible Sylow choices in every finite quotient. -/
def CompatibleSylowFamily.closedSubgroup {G : ProfiniteGrp.{u}} {p : ℕ}
    {hp : p.Prime} (s : G.CompatibleSylowFamily p hp) : ClosedSubgroup G :=
  CompatibleSubgroups.closedReconstruction G
    (fun U => (s.at U : Subgroup (G ⧸ (U : Subgroup G))))

/-- The image of the reconstructed closed subgroup is exactly the prescribed Sylow
subgroup in each open-normal quotient. -/
theorem CompatibleSylowFamily.map_closedSubgroup {G : ProfiniteGrp.{u}} {p : ℕ}
    {hp : p.Prime} (s : G.CompatibleSylowFamily p hp) (U : OpenNormalSubgroup G) :
    s.closedSubgroup.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) =
      (s.at U : Subgroup (G ⧸ U.toSubgroup)) := by
  apply CompatibleSubgroups.map_reconstruct
  intro V W h
  exact s.map_at_subgroup h

/-- Every finite quotient image of the reconstructed closed subgroup is a
`p`-group, with no claim about its underlying abstract subgroup of `G`. -/
theorem CompatibleSylowFamily.isPGroup_image {G : ProfiniteGrp.{u}} {p : ℕ}
    {hp : p.Prime} (s : G.CompatibleSylowFamily p hp) (U : OpenNormalSubgroup G) :
    IsPGroup p (s.closedSubgroup.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) := by
  rw [s.map_closedSubgroup U]
  exact (s.at U).isPGroup'

/-- There is a closed subgroup whose image in every finite open-normal quotient
is a Sylow `p`-subgroup. -/
theorem exists_closedSylow (G : ProfiniteGrp.{u}) (p : ℕ) (hp : p.Prime) :
    ∃ P : ClosedSubgroup G, ∀ U : OpenNormalSubgroup G,
      ∃ Q : Sylow p (G ⧸ U.toSubgroup),
        P.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) = Q := by
  obtain ⟨s⟩ := G.exists_compatibleSylowFamily p hp
  exact ⟨s.closedSubgroup, fun U => ⟨s.at U, s.map_closedSubgroup U⟩⟩

/-- A Sylow subgroup in any prescribed finite quotient is the exact image of a
closed subgroup with Sylow images at every finite open-normal quotient. -/
theorem exists_closedSylow_with (G : ProfiniteGrp.{u}) (p : ℕ) (hp : p.Prime)
    (U : OpenNormalSubgroup G) (Q : Sylow p (G ⧸ U.toSubgroup)) :
    ∃ P : ClosedSubgroup G,
      P.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) = (Q : Subgroup (G ⧸ U.toSubgroup)) ∧
      ∀ V : OpenNormalSubgroup G, ∃ R : Sylow p (G ⧸ V.toSubgroup),
        P.toSubgroup.map (QuotientGroup.mk' V.toSubgroup) = R := by
  obtain ⟨s, hs⟩ := G.exists_compatibleSylowFamily_with p hp U Q
  refine ⟨s.closedSubgroup, ?_, fun V => ⟨s.at V, s.map_closedSubgroup V⟩⟩
  rw [s.map_closedSubgroup]
  exact congrArg (fun R : Sylow p (G ⧸ U.toSubgroup) =>
    (R : Subgroup (G ⧸ U.toSubgroup))) hs

/-- Bounded maximality: a subgroup containing a closed subgroup with Sylow images
coincides with it if *every actual finite quotient image* is a `p`-group.
The larger subgroup need not be closed. -/
theorem eq_closedSylow_of_le_of_isPGroup_images {G : ProfiniteGrp.{u}} {p : ℕ}
    (P : ClosedSubgroup G)
    (hP : ∀ U : OpenNormalSubgroup G, ∃ Q : Sylow p (G ⧸ U.toSubgroup),
      P.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) = Q)
    (H : Subgroup G) (hPH : P.toSubgroup ≤ H)
    (hH : ∀ U : OpenNormalSubgroup G,
      IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup))) :
    H = P.toSubgroup := by
  apply le_antisymm
  · rw [CompatibleSubgroups.closed_eq_iInf_images G P]
    apply le_iInf
    intro U
    obtain ⟨Q, hQ⟩ := hP U
    have hle : (Q : Subgroup (G ⧸ U.toSubgroup)) ≤
        H.map (QuotientGroup.mk' U.toSubgroup) := by
      rw [← hQ]
      exact Subgroup.map_mono hPH
    have heq : H.map (QuotientGroup.mk' U.toSubgroup) =
        P.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) :=
      (Q.is_maximal' (hH U) hle).trans hQ.symm
    calc
      H ≤ (H.map (QuotientGroup.mk' U.toSubgroup)).comap
          (QuotientGroup.mk' U.toSubgroup) :=
        Subgroup.le_comap_map (QuotientGroup.mk' U.toSubgroup) H
      _ = (P.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).comap
          (QuotientGroup.mk' U.toSubgroup) := by rw [heq]
  · exact hPH

end ProfiniteGrp
