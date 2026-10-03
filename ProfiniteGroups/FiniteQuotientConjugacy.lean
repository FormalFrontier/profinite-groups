/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module

public import ProfiniteGroups.CompatibleSubgroups
public import Mathlib.Algebra.Group.End

/-!
# Conjugacy of closed subgroups in finite quotients

Closed subgroups of a profinite group are conjugate precisely when their images are conjugate
in each finite open-normal quotient. No compatibility between the quotient conjugators is needed.
Closedness is used to recover subgroup equality from equality of all finite quotient images.
-/

@[expose] public section

set_option warningAsError true

namespace ProfiniteGrp.FiniteQuotientConjugacy

variable (G : ProfiniteGrp)

private theorem map_conj {A B : Type*} [Group A] [Group B]
    (f : A →* B) (H : Subgroup A) (g : A) :
    (H.map (MulAut.conj g).toMonoidHom).map f =
      (H.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

private theorem image_transition (H : Subgroup G)
    (U V : OpenNormalSubgroup G) (h : U ≤ V) :
    (H.map (QuotientGroup.mk' U.toSubgroup)).map
      (CompatibleSubgroups.transition G U V h) =
        H.map (QuotientGroup.mk' V.toSubgroup) := by
  rw [Subgroup.map_map]
  congr 1

private theorem conjugate_image_transition (H K : Subgroup G)
    (U V : OpenNormalSubgroup G) (h : U ≤ V)
    (a : G ⧸ U.toSubgroup)
    (ha : (H.map (QuotientGroup.mk' U.toSubgroup)).map
        (MulAut.conj a).toMonoidHom = K.map (QuotientGroup.mk' U.toSubgroup)) :
    (H.map (QuotientGroup.mk' V.toSubgroup)).map
        (MulAut.conj (CompatibleSubgroups.transition G U V h a)).toMonoidHom =
      K.map (QuotientGroup.mk' V.toSubgroup) := by
  rw [← image_transition G H U V h,
    ← map_conj (CompatibleSubgroups.transition G U V h)
      (H.map (QuotientGroup.mk' U.toSubgroup)) a,
    ha, image_transition G K U V h]

private def conjugators (H K : ClosedSubgroup G) (U : OpenNormalSubgroup G) : Set G :=
  {g | (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).map
      (MulAut.conj (QuotientGroup.mk' U.toSubgroup g)).toMonoidHom =
        K.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)}

private theorem isClosed_conjugators (H K : ClosedSubgroup G)
    (U : OpenNormalSubgroup G) : IsClosed (conjugators G H K U) := by
  let S : Set (G ⧸ U.toSubgroup) :=
    {a | (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).map
      (MulAut.conj a).toMonoidHom = K.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)}
  have : DiscreteTopology (G ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
  change IsClosed ((QuotientGroup.mk' U.toSubgroup) ⁻¹' S)
  exact (isClosed_discrete S).preimage (QuotientGroup.continuous_mk (N := U.toSubgroup))

private def conjugateClosed (H : ClosedSubgroup G) (g : G) : ClosedSubgroup G where
  toSubgroup := H.toSubgroup.map (MulAut.conj g).toMonoidHom
  isClosed' := by
    rw [Subgroup.map_equiv_eq_comap_symm']
    apply H.isClosed'.preimage
    convert IsTopologicalGroup.continuous_conj g⁻¹ using 1
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply, inv_inv]

/-- If two closed subgroups are conjugate in every finite open-normal quotient,
they are conjugate by one element of the profinite group. Quotient conjugators
need not be selected compatibly. -/
theorem exists_conjugator_of_forall_quotients (H K : ClosedSubgroup G)
    (h : ∀ U : OpenNormalSubgroup G, ∃ a : G ⧸ U.toSubgroup,
      (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).map
          (MulAut.conj a).toMonoidHom =
        K.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) :
    ∃ g : G, H.toSubgroup.map (MulAut.conj g).toMonoidHom = K.toSubgroup := by
  classical
  have hfinite (F : Finset (OpenNormalSubgroup G)) :
      (Set.univ ∩ ⋂ U ∈ F, conjugators G H K U).Nonempty := by
    by_cases hF : F.Nonempty
    · let W : OpenNormalSubgroup G := F.inf' hF id
      obtain ⟨a, ha⟩ := h W
      obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective W.toSubgroup a
      refine ⟨g, ⟨Set.mem_univ g, ?_⟩⟩
      simp only [Set.mem_iInter]
      intro U hUF
      change (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).map
          (MulAut.conj (QuotientGroup.mk' U.toSubgroup g)).toMonoidHom =
        K.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)
      have hWU : W ≤ U := Finset.inf'_le id hUF
      have ht := conjugate_image_transition G H.toSubgroup K.toSubgroup W U hWU a ha
      simpa only [← hg, CompatibleSubgroups.transition_mk] using ht
    · have hEmpty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      subst F
      exact ⟨1, by simp⟩
  obtain ⟨g, _, hg⟩ := (isCompact_univ.inter_iInter_nonempty
    (conjugators G H K) (isClosed_conjugators G H K) hfinite)
  refine ⟨g, ?_⟩
  have hEq : conjugateClosed G H g = K :=
    CompatibleSubgroups.ext_images G (conjugateClosed G H g) K (by
      intro U
      rw [conjugateClosed, map_conj]
      exact Set.mem_iInter.mp hg U)
  exact congrArg ClosedSubgroup.toSubgroup hEq

/-- Closed subgroups of a profinite group are conjugate exactly when their
images are conjugate independently in each finite open-normal quotient. -/
theorem exists_conjugator_iff_forall_quotients (H K : ClosedSubgroup G) :
    (∃ g : G, H.toSubgroup.map (MulAut.conj g).toMonoidHom = K.toSubgroup) ↔
      ∀ U : OpenNormalSubgroup G, ∃ a : G ⧸ U.toSubgroup,
        (H.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).map
            (MulAut.conj a).toMonoidHom =
          K.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) := by
  constructor
  · rintro ⟨g, hg⟩ U
    refine ⟨QuotientGroup.mk' U.toSubgroup g, ?_⟩
    rw [← map_conj (QuotientGroup.mk' U.toSubgroup) H.toSubgroup g, hg]
  · exact exists_conjugator_of_forall_quotients G H K

end ProfiniteGrp.FiniteQuotientConjugacy
