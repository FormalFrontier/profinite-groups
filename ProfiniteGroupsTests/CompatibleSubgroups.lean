/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.CompatibleSubgroups
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Topology.Order

public section

set_option warningAsError true

/-! # Quotient-image reconstruction clients -/

namespace Tests.CompatibleSubgroups

open ProfiniteGrp.CompatibleSubgroups

variable (G : ProfiniteGrp)

example (L : ClosedSubgroup G) :
    Compatible G (fun U : OpenNormalSubgroup G =>
      L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) := by
  intro U V h
  rw [Subgroup.map_map]
  congr 1

example (U : OpenNormalSubgroup (ProfiniteGrp.of PUnit)) :
    (reconstruct (ProfiniteGrp.of PUnit)
      (fun V : OpenNormalSubgroup (ProfiniteGrp.of PUnit) =>
        (⊥ : Subgroup ((ProfiniteGrp.of PUnit) ⧸ V.toSubgroup)))).map
        (QuotientGroup.mk' U.toSubgroup) = ⊥ := by
  apply map_reconstruct
  intro V W h
  simp

end Tests.CompatibleSubgroups
