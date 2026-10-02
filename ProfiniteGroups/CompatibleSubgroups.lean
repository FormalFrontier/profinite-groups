/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Algebra.Group.Subgroup.Ker

@[expose] public section

set_option warningAsError true

/-!
# Closed subgroups from finite quotient images

Compatible subgroup images at every open normal quotient reconstruct a unique closed
subgroup. Compatibility requires equality under each finer-to-coarser quotient map.
-/

namespace ProfiniteGrp.CompatibleSubgroups

variable (G : ProfiniteGrp)

/-- The quotient transition from `G/U` to `G/V` for `U ≤ V`. -/
def transition (U V : OpenNormalSubgroup G) (h : U ≤ V) :
    G ⧸ U.toSubgroup →* G ⧸ V.toSubgroup :=
  QuotientGroup.map U.toSubgroup V.toSubgroup (MonoidHom.id G)
    (by
      intro g hg
      exact h hg)

@[simp]
theorem transition_mk (U V : OpenNormalSubgroup G) (h : U ≤ V) (g : G) :
    transition G U V h (QuotientGroup.mk' U.toSubgroup g) =
      QuotientGroup.mk' V.toSubgroup g :=
  rfl

/-- Subgroups in all finite open-normal quotients of `G`. -/
abbrev Family : Type _ := ∀ U : OpenNormalSubgroup G, Subgroup (G ⧸ U.toSubgroup)

/-- Equality of the quotient images under every transition `G/U → G/V` with `U ≤ V`. -/
def Compatible (S : Family G) : Prop :=
  ∀ ⦃U V : OpenNormalSubgroup G⦄ (h : U ≤ V),
    (S U).map (transition G U V h) = S V

/-- The subgroup of elements satisfying every quotient condition in a family. -/
def reconstruct (S : Family G) : Subgroup G :=
  ⨅ U : OpenNormalSubgroup G, (S U).comap (QuotientGroup.mk' U.toSubgroup)

@[simp]
theorem mem_reconstruct (S : Family G) (g : G) :
    g ∈ reconstruct G S ↔
      ∀ U : OpenNormalSubgroup G, QuotientGroup.mk' U.toSubgroup g ∈ S U := by
  simp only [reconstruct, Subgroup.mem_iInf, Subgroup.mem_comap]

private theorem coordinate_closed (S : Family G) (U : OpenNormalSubgroup G) :
    IsClosed ((S U).comap (QuotientGroup.mk' U.toSubgroup) : Set G) := by
  have : DiscreteTopology (G ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
  exact IsClosed.preimage (QuotientGroup.continuous_mk (N := U.toSubgroup))
    (isClosed_discrete _)

/-- Reconstruction is closed even without the image-compatibility hypothesis. -/
theorem isClosed_reconstruct (S : Family G) : IsClosed (reconstruct G S : Set G) := by
  simpa only [reconstruct, Subgroup.coe_iInf] using
    (isClosed_iInter (fun U => coordinate_closed G S U))

/-- The closed subgroup represented by a family of quotient subgroups. -/
def closedReconstruction (S : Family G) : ClosedSubgroup G where
  toSubgroup := reconstruct G S
  isClosed' := isClosed_reconstruct G S

@[simp]
theorem closedReconstruction_toSubgroup (S : Family G) :
    (closedReconstruction G S).toSubgroup = reconstruct G S := rfl

private theorem common_refinement (U : OpenNormalSubgroup G)
    (F : Finset (OpenNormalSubgroup G)) :
    ∃ W : OpenNormalSubgroup G, W ≤ U ∧ ∀ V ∈ F, W ≤ V := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨U, le_refl U, by simp⟩
  | @insert V F hV ih =>
    obtain ⟨W, hWU, hWF⟩ := ih
    refine ⟨W ⊓ V, (inf_le_left).trans hWU, ?_⟩
    intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hTF
    · exact inf_le_right
    · exact (inf_le_left).trans (hWF T hTF)

/-- Every compatible family occurs as the exact images of its reconstruction. -/
theorem map_reconstruct (S : Family G) (hS : Compatible G S)
    (U : OpenNormalSubgroup G) :
    (reconstruct G S).map (QuotientGroup.mk' U.toSubgroup) = S U := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr (iInf_le _ U)
  · intro a ha
    let B : Set G := (QuotientGroup.mk' U.toSubgroup) ⁻¹' ({a} : Set (G ⧸ U.toSubgroup))
    let C (V : OpenNormalSubgroup G) : Set G :=
      (QuotientGroup.mk' V.toSubgroup) ⁻¹' (S V : Set (G ⧸ V.toSubgroup))
    have hB : IsCompact B := by
      have : DiscreteTopology (G ⧸ U.toSubgroup) := QuotientGroup.discreteTopology U.isOpen
      exact (IsClosed.preimage (QuotientGroup.continuous_mk (N := U.toSubgroup))
        (isClosed_discrete ({a} : Set (G ⧸ U.toSubgroup)))).isCompact
    have hC (V : OpenNormalSubgroup G) : IsClosed (C V) := by
      change IsClosed ((S V).comap (QuotientGroup.mk' V.toSubgroup) : Set G)
      exact coordinate_closed G S V
    have hfinite (F : Finset (OpenNormalSubgroup G)) :
        (B ∩ ⋂ V ∈ F, C V).Nonempty := by
      obtain ⟨W, hWU, hWF⟩ := common_refinement G U F
      have haW : a ∈ (S W).map (transition G W U hWU) := by
        rw [hS hWU]
        exact ha
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp haW
      obtain ⟨g, hgb⟩ := QuotientGroup.mk'_surjective W.toSubgroup b
      refine ⟨g, ?_, ?_⟩
      · change QuotientGroup.mk' U.toSubgroup g = a
        calc
          QuotientGroup.mk' U.toSubgroup g =
              transition G W U hWU (QuotientGroup.mk' W.toSubgroup g) :=
            (transition_mk G W U hWU g).symm
          _ = transition G W U hWU b := by rw [hgb]
          _ = a := hba
      · simp only [Set.mem_iInter]
        intro V hVF
        change QuotientGroup.mk' V.toSubgroup g ∈ S V
        rw [← hS (hWF V hVF), ← transition_mk G W V (hWF V hVF), hgb]
        exact Subgroup.mem_map_of_mem _ hb
    obtain ⟨g, hgB, hgC⟩ := hB.inter_iInter_nonempty C hC hfinite
    apply Subgroup.mem_map.mpr
    refine ⟨g, ?_, hgB⟩
    change g ∈ ⨅ V : OpenNormalSubgroup G,
      (S V).comap (QuotientGroup.mk' V.toSubgroup)
    exact Subgroup.mem_iInf.mpr (fun V => Set.mem_iInter.mp hgC V)

/-- A closed subgroup is determined by all of its finite quotient images. -/
theorem closed_eq_iInf_images (L : ClosedSubgroup G) :
    L.toSubgroup = ⨅ U : OpenNormalSubgroup G,
      (L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).comap
        (QuotientGroup.mk' U.toSubgroup) := by
  apply le_antisymm
  · exact le_iInf (fun U =>
      Subgroup.le_comap_map (QuotientGroup.mk' U.toSubgroup) L.toSubgroup)
  · calc
      (⨅ U : OpenNormalSubgroup G,
          (L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).comap
            (QuotientGroup.mk' U.toSubgroup)) ≤
          sInf {K : Subgroup G | IsOpen (K : Set G) ∧ L.toSubgroup ≤ K} := by
        apply le_sInf
        intro K hK
        obtain ⟨U, hUK⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
          hK.1 K.one_mem
        have hU_le_K : U.toSubgroup ≤ K := hUK
        calc
          (⨅ U : OpenNormalSubgroup G,
              (L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).comap
                (QuotientGroup.mk' U.toSubgroup)) ≤
              (L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).comap
                (QuotientGroup.mk' U.toSubgroup) := iInf_le _ U
          _ = L.toSubgroup ⊔ U.toSubgroup := by
            rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
          _ ≤ K := sup_le hK.2 hU_le_K
      _ = L.toSubgroup := (ProfiniteGrp.closedSubgroup_eq_sInf_open L).symm

/-- Closed subgroups with equal images in every open-normal quotient are equal. -/
theorem ext_images (L K : ClosedSubgroup G)
    (h : ∀ U : OpenNormalSubgroup G,
      L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) =
        K.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) : L = K := by
  apply ClosedSubgroup.toSubgroup_injective
  calc
    L.toSubgroup = ⨅ U : OpenNormalSubgroup G,
        (L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).comap
          (QuotientGroup.mk' U.toSubgroup) := closed_eq_iInf_images G L
    _ = ⨅ U : OpenNormalSubgroup G,
        (K.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)).comap
          (QuotientGroup.mk' U.toSubgroup) := by
        congr 1
        funext U
        rw [h U]
    _ = K.toSubgroup := (closed_eq_iInf_images G K).symm

/-- The reconstructed subgroup is the unique closed subgroup with the given images. -/
theorem closedReconstruction_unique (S : Family G) (hS : Compatible G S)
    (L : ClosedSubgroup G)
    (hL : ∀ U : OpenNormalSubgroup G,
      L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup) = S U) :
    L = closedReconstruction G S := by
  apply ext_images G
  intro U
  rw [hL U]
  exact (map_reconstruct G S hS U).symm

/-- A closed subgroup is reconstructed from its images in every finite quotient. -/
theorem closedReconstruction_images (L : ClosedSubgroup G) :
    closedReconstruction G
        (fun U : OpenNormalSubgroup G =>
          L.toSubgroup.map (QuotientGroup.mk' U.toSubgroup)) = L := by
  apply ClosedSubgroup.toSubgroup_injective
  exact (closed_eq_iInf_images G L).symm

end ProfiniteGrp.CompatibleSubgroups
