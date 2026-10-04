/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ContinuousSection
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Closed coset spaces and normal quotients of profinite groups

A closed subgroup of a profinite group determines a profinite space of left
cosets, whether or not the subgroup is normal. For a closed normal subgroup,
the same quotient topology gives a profinite group and a continuous quotient
homomorphism. The constructions use Mathlib's quotient types and topology.

Closedness is essential for Hausdorffness: a quotient by a nonclosed subgroup
need not even be a T1 space. No openness or finite-index condition is imposed.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1 (closed subgroups and
  quotient spaces); this motivates the quotient construction, not its universe-specific
  API.
- Mathlib, `Mathlib.Topology.Algebra.Group.Quotient` and
  `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic` (quotient topology and
  profinite-group structure).
-/

@[expose] public section

open CategoryTheory

universe u

namespace ProfiniteGrp

/-- The profinite space of cosets of any closed subgroup. Its carrier and
topology are those of Mathlib's group quotient.

The construction is motivated by Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
Ch. I §1 (closed subgroups and cosets) and uses Mathlib’s group quotient topology. -/
def closedCosetSpace (G : ProfiniteGrp.{u}) (H : ClosedSubgroup G) : Profinite.{u} := by
  letI : IsClosed (H.toSubgroup : Set G) := H.isClosed'
  exact Profinite.of (G ⧸ H.toSubgroup)

/-- The underlying type of the closed-coset space is the usual quotient. -/
@[simp]
theorem coe_closedCosetSpace (G : ProfiniteGrp.{u}) (H : ClosedSubgroup G) :
    (G.closedCosetSpace H : Type u) = (G ⧸ H.toSubgroup) := rfl

/-- The continuous projection to the profinite coset space of a closed subgroup. -/
def closedCosetProj (G : ProfiniteGrp.{u}) (H : ClosedSubgroup G) :
    G.toProfinite ⟶ G.closedCosetSpace H :=
  ConcreteCategory.ofHom ⟨QuotientGroup.mk, QuotientGroup.continuous_mk⟩

@[simp]
theorem closedCosetProj_apply (G : ProfiniteGrp.{u}) (H : ClosedSubgroup G) (g : G) :
    G.closedCosetProj H g = QuotientGroup.mk g := rfl

theorem closedCosetProj_surjective (G : ProfiniteGrp.{u}) (H : ClosedSubgroup G) :
    Function.Surjective (G.closedCosetProj H) :=
  QuotientGroup.mk_surjective

/-- The coset projection gives precisely the quotient topology. -/
theorem closedCosetProj_isQuotientMap (G : ProfiniteGrp.{u}) (H : ClosedSubgroup G) :
    Topology.IsQuotientMap (G.closedCosetProj H) :=
  QuotientGroup.isQuotientMap_mk H.toSubgroup

/-- The profinite group quotient by a closed normal subgroup. -/
def closedNormalQuotient (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) : ProfiniteGrp.{u} := by
  letI : N.toSubgroup.Normal := hN
  letI : IsClosed (N.toSubgroup : Set G) := N.isClosed'
  exact ProfiniteGrp.of (G ⧸ N.toSubgroup)

/-- The underlying type of a closed normal quotient is the usual group quotient. -/
@[simp]
theorem coe_closedNormalQuotient (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) :
    (G.closedNormalQuotient N hN : Type u) = (G ⧸ N.toSubgroup) := rfl

/-- The canonical continuous homomorphism to a closed normal quotient. -/
def closedNormalQuotientProj (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) : G ⟶ G.closedNormalQuotient N hN := by
  letI : N.toSubgroup.Normal := hN
  exact ConcreteCategory.ofHom
    ⟨QuotientGroup.mk' N.toSubgroup, QuotientGroup.continuous_mk⟩

@[simp]
theorem closedNormalQuotientProj_apply (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) (g : G) :
    G.closedNormalQuotientProj N hN g = QuotientGroup.mk g := rfl

theorem closedNormalQuotientProj_surjective (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) :
    Function.Surjective (G.closedNormalQuotientProj N hN) :=
  QuotientGroup.mk'_surjective N.toSubgroup

/-- The normal quotient carries exactly Mathlib's quotient topology. -/
theorem closedNormalQuotientProj_isQuotientMap (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) :
    Topology.IsQuotientMap (G.closedNormalQuotientProj N hN) :=
  QuotientGroup.isQuotientMap_mk N.toSubgroup

/-- The canonical quotient homomorphism has exactly the specified kernel. -/
@[simp]
theorem closedNormalQuotientProj_ker (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) :
    (G.closedNormalQuotientProj N hN).hom.ker = N.toSubgroup :=
  QuotientGroup.ker_mk' N.toSubgroup

/-- The profinite space underlying a normal quotient agrees with its coset space. -/
theorem closedNormalQuotient_toProfinite (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) :
    (G.closedNormalQuotient N hN).toProfinite = G.closedCosetSpace N := by
  rfl

/-- Forgetting the normal quotient homomorphism yields the closed-coset
projection, after identifying their profinite codomains. -/
theorem closedNormalQuotientProj_toProfinite (G : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) :
    (forget₂ ProfiniteGrp Profinite).map (G.closedNormalQuotientProj N hN) ≫
      eqToHom (G.closedNormalQuotient_toProfinite N hN) = G.closedCosetProj N := by
  ext g
  rfl

/-- A continuous homomorphism killing a closed normal subgroup descends to its quotient. -/
def closedNormalQuotientDescend (G K : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) (f : G ⟶ K)
    (hNker : N.toSubgroup ≤ f.hom.ker) : G.closedNormalQuotient N hN ⟶ K := by
  letI : N.toSubgroup.Normal := hN
  refine ConcreteCategory.ofHom ⟨QuotientGroup.lift N.toSubgroup f.hom.toMonoidHom hNker, ?_⟩
  apply (QuotientGroup.isQuotientMap_mk N.toSubgroup).continuous_iff.mpr
  change Continuous f.hom
  exact f.hom.continuous

@[simp]
theorem closedNormalQuotientDescend_apply_mk (G K : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) (f : G ⟶ K) (hNker : N.toSubgroup ≤ f.hom.ker)
    (g : G) :
    G.closedNormalQuotientDescend K N hN f hNker (G.closedNormalQuotientProj N hN g) = f g :=
  rfl

/-- Morphisms out of a normal quotient agree if they agree after projection. -/
theorem closedNormalQuotient_hom_ext (G K : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) (f g : G.closedNormalQuotient N hN ⟶ K)
    (h : G.closedNormalQuotientProj N hN ≫ f = G.closedNormalQuotientProj N hN ≫ g) :
    f = g := by
  ext q
  obtain ⟨x, rfl⟩ := G.closedNormalQuotientProj_surjective N hN q
  exact congrArg (fun t : G ⟶ K ↦ t x) h

/-- Descending a homomorphism recovers it after the quotient projection. -/
theorem closedNormalQuotientDescend_comp (G K : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) (f : G ⟶ K) (hNker : N.toSubgroup ≤ f.hom.ker) :
    G.closedNormalQuotientProj N hN ≫ G.closedNormalQuotientDescend K N hN f hNker = f := by
  ext g
  exact G.closedNormalQuotientDescend_apply_mk K N hN f hNker g

/-- A morphism from a closed normal quotient is determined by its composite
with the quotient projection. -/
theorem closedNormalQuotientDescend_unique (G K : ProfiniteGrp.{u}) (N : ClosedSubgroup G)
    (hN : N.toSubgroup.Normal) (f : G ⟶ K) (hNker : N.toSubgroup ≤ f.hom.ker)
    (descended : G.closedNormalQuotient N hN ⟶ K)
    (hcomp : G.closedNormalQuotientProj N hN ≫ descended = f) :
    descended = G.closedNormalQuotientDescend K N hN f hNker := by
  exact G.closedNormalQuotient_hom_ext K N hN _ _
    (hcomp.trans (G.closedNormalQuotientDescend_comp K N hN f hNker).symm)

end ProfiniteGrp
