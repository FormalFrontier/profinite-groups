/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProfiniteGroups.FiniteQuotientConjugacy
public import Mathlib.Algebra.Group.PUnit

/-!
# Examples of finite-quotient conjugacy

Both directions of the conjugacy criterion apply to arbitrary closed subgroups. Equal subgroups
have identity conjugators in every quotient, and the trivial profinite group has only one closed
subgroup.
-/

public section

set_option warningAsError true

namespace ProfiniteGroupsTests.FiniteQuotientConjugacy

open ProfiniteGrp.FiniteQuotientConjugacy

variable (G : ProfiniteGrp) (H K : ClosedSubgroup G)

example (h : H.toSubgroup.map (MulAut.conj (1 : G)).toMonoidHom = K.toSubgroup)
    (U : OpenNormalSubgroup G) :
    ∃ a : G ⧸ U.toSubgroup,
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).map
          (MulAut.conj a).toMonoidHom =
        K.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) :=
  (exists_conjugator_iff_forall_quotients G H K).mp ⟨1, h⟩ U

example : ∃ g : G, H.toSubgroup.map (MulAut.conj g).toMonoidHom = H.toSubgroup := by
  apply exists_conjugator_of_forall_quotients G H H
  intro U
  refine ⟨1, ?_⟩
  apply Subgroup.ext
  intro x
  rw [Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_one, one_mul, mul_one]

example (U : OpenNormalSubgroup G) :
    ∃ a : G ⧸ U.toSubgroup,
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).map
          (MulAut.conj a).toMonoidHom =
        H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) := by
  exact (exists_conjugator_iff_forall_quotients G H H).mp
    ⟨1, by
      apply Subgroup.ext
      intro x
      rw [Subgroup.mem_map_equiv]
      simp only [MulAut.conj_symm_apply, inv_one, one_mul, mul_one]⟩ U

example (H K : ClosedSubgroup (ProfiniteGrp.of PUnit)) : H = K := by
  apply SetLike.ext
  intro x
  have hx : x = 1 := Subsingleton.elim x 1
  subst x
  simp

end ProfiniteGroupsTests.FiniteQuotientConjugacy
