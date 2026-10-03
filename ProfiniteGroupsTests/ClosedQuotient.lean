/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ClosedQuotient
public import ProfiniteGroups.PrimewisePadic
public import ProfiniteGroups.Procyclic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index

/-!
# Closed quotient clients

The point stabilizer in the symmetric group on three points is closed but not
normal, yet its coset space is profinite and has three points. A finite cyclic
group gives a nontrivial normal quotient with descent. The trivial subgroup
of the additive two-adic integers is closed but not open.
-/

@[expose] public section

open CategoryTheory ProfiniteGrp

universe u

namespace ClosedQuotientTests

/-- The finite symmetric group on three points, as a profinite group. -/
def symmetricThree : ProfiniteGrp :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm (Fin 3)))

/-- The closed subgroup of permutations fixing the first point. -/
def pointStabilizer : ClosedSubgroup symmetricThree where
  toSubgroup := MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3)
  isClosed' := by
    have hFinite : Finite symmetricThree := by
      change Finite (Equiv.Perm (Fin 3))
      infer_instance
    exact ((@Set.finite_univ symmetricThree hFinite).subset (Set.subset_univ _)).isClosed

/-- The point stabilizer is not normal: conjugating a swap of the other two
points by a swap involving the first point moves the fixed point. -/
theorem pointStabilizer_not_normal : ¬ pointStabilizer.toSubgroup.Normal := by
  intro hnormal
  have hswap : Equiv.swap (1 : Fin 3) 2 ∈ pointStabilizer.toSubgroup := by
    change Equiv.swap (1 : Fin 3) 2 (0 : Fin 3) = 0
    decide
  have hconj := hnormal.conj_mem (Equiv.swap (1 : Fin 3) 2) hswap
    (Equiv.swap (0 : Fin 3) 1)
  have hnot : Equiv.swap (0 : Fin 3) (1 : Fin 3) *
      Equiv.swap (1 : Fin 3) (2 : Fin 3) *
      (Equiv.swap (0 : Fin 3) (1 : Fin 3))⁻¹ ∉ pointStabilizer.toSubgroup := by
    change (Equiv.swap (0 : Fin 3) (1 : Fin 3) *
      Equiv.swap (1 : Fin 3) (2 : Fin 3) *
      (Equiv.swap (0 : Fin 3) (1 : Fin 3))⁻¹) (0 : Fin 3) ≠ 0
    decide
  exact hnot hconj

/-- The nonnormal stabilizer nevertheless gives a three-point profinite space. -/
theorem symmetricThree_cosets : Nat.card (symmetricThree.closedCosetSpace pointStabilizer) = 3 := by
  change (MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3)).index = 3
  simpa using (MulAction.index_stabilizer_of_transitive (Equiv.Perm (Fin 3)) (0 : Fin 3))

/-- Reduction from the cyclic group of order six to that of order three. -/
def cyclicSixToThree : finiteCyclic 6 ⟶ finiteCyclic 3 :=
  ofFiniteGrpHom <| FiniteGrp.ofHom
    ((ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3)).toAddMonoidHom.toMultiplicative)

/-- Its kernel is a closed normal subgroup of the cyclic group of order six. -/
def cyclicSixKernel : ClosedSubgroup (finiteCyclic 6) where
  toSubgroup := cyclicSixToThree.hom.ker
  isClosed' := by
    change IsClosed (cyclicSixToThree.hom ⁻¹' ({1} : Set (finiteCyclic 3)))
    exact isClosed_singleton.preimage cyclicSixToThree.hom.continuous

theorem cyclicSixKernel_normal : cyclicSixKernel.toSubgroup.Normal := by
  change cyclicSixToThree.hom.ker.Normal
  infer_instance

/-- Reduction modulo three has a proper kernel in the cyclic group of order six. -/
theorem cyclicSixKernel_proper : cyclicSixKernel.toSubgroup ≠ ⊤ := by
  intro heq
  have hmem : finiteCyclicGenerator 6 ∈ cyclicSixKernel.toSubgroup := by
    rw [heq]
    exact Subgroup.mem_top _
  have hnonzero : cyclicSixToThree (finiteCyclicGenerator 6) ≠ 1 := by
    change (ZMod.castHom (by decide : 3 ∣ 6) (ZMod 3)) (1 : ZMod 6) ≠ 0
    simp
  exact hnonzero (MonoidHom.mem_ker.mp hmem)

/-- The quotient is nontrivial and its universal morphism recovers reduction
modulo three after projection. -/
theorem cyclicSix_descends :
    Nontrivial ((finiteCyclic 6).closedNormalQuotient cyclicSixKernel cyclicSixKernel_normal) ∧
      (finiteCyclic 6).closedNormalQuotientProj cyclicSixKernel cyclicSixKernel_normal ≫
        (finiteCyclic 6).closedNormalQuotientDescend (finiteCyclic 3)
          cyclicSixKernel cyclicSixKernel_normal cyclicSixToThree le_rfl = cyclicSixToThree := by
  constructor
  · change Nontrivial (finiteCyclic 6 ⧸ cyclicSixKernel.toSubgroup)
    rw [QuotientGroup.nontrivial_iff]
    exact cyclicSixKernel_proper
  · exact (finiteCyclic 6).closedNormalQuotientDescend_comp
      (finiteCyclic 3) cyclicSixKernel cyclicSixKernel_normal cyclicSixToThree le_rfl

/-- The group quotient projection also surjects onto the associated coset space. -/
theorem cyclicSix_projection_to_cosets_surjective :
    Function.Surjective
      ((forget₂ ProfiniteGrp Profinite).map
        ((finiteCyclic 6).closedNormalQuotientProj cyclicSixKernel cyclicSixKernel_normal) ≫
          eqToHom ((finiteCyclic 6).closedNormalQuotient_toProfinite
            cyclicSixKernel cyclicSixKernel_normal)) := by
  rw [(finiteCyclic 6).closedNormalQuotientProj_toProfinite]
  exact (finiteCyclic 6).closedCosetProj_surjective cyclicSixKernel

/-- Descent of the quotient projection is the identity, even for a nontrivial quotient. -/
theorem cyclicSix_projection_descend_id :
    (finiteCyclic 6).closedNormalQuotientDescend
      ((finiteCyclic 6).closedNormalQuotient cyclicSixKernel cyclicSixKernel_normal)
      cyclicSixKernel cyclicSixKernel_normal
      ((finiteCyclic 6).closedNormalQuotientProj cyclicSixKernel cyclicSixKernel_normal)
      (by rw [(finiteCyclic 6).closedNormalQuotientProj_ker]) = 𝟙 _ := by
  symm
  apply (finiteCyclic 6).closedNormalQuotientDescend_unique
  simp

/-- The multiplicative presentation of the additive two-adic integers. -/
noncomputable def twoAdic : ProfiniteGrp :=
  padicFactor ⟨2, by decide⟩

/-- The zero subgroup of the two-adic integers is closed. -/
noncomputable def twoAdicZero : ClosedSubgroup twoAdic where
  toSubgroup := ⊥
  isClosed' := by
    change IsClosed ({1} : Set twoAdic)
    exact isClosed_singleton

/-- The zero subgroup of the two-adic integers is not open. -/
theorem twoAdicZero_not_open :
    ¬IsOpen (twoAdicZero.toSubgroup : Set twoAdic) := by
  intro hopen
  have hDiscrete : DiscreteTopology twoAdic :=
    discreteTopology_iff_isOpen_singleton_one.mpr (by
      change IsOpen ({1} : Set twoAdic) at hopen
      exact hopen)
  have hFinite : Finite twoAdic :=
    @finite_of_compact_of_discrete twoAdic _ _ hDiscrete
  have hInfinite : Infinite twoAdic := by
    change Infinite (Multiplicative (ULift ℤ_[2]))
    infer_instance
  exact @not_finite twoAdic hInfinite hFinite

/-- The closed nonopen two-adic zero subgroup still admits a profinite coset
space with the quotient topology. -/
theorem twoAdicZero_coset_projection :
    ¬IsOpen (twoAdicZero.toSubgroup : Set twoAdic) ∧
      Topology.IsQuotientMap (twoAdic.closedCosetProj twoAdicZero) :=
  ⟨twoAdicZero_not_open, twoAdic.closedCosetProj_isQuotientMap twoAdicZero⟩

/-- The construction also applies to the full subgroup of the trivial group. -/
theorem trivial_top_quotient_subsingleton :
    Subsingleton ((ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit)).closedNormalQuotient
      ⟨⊤, by
        change IsClosed (Set.univ : Set PUnit)
        exact isClosed_univ⟩
      inferInstance) := by
  change Subsingleton (PUnit ⧸ (⊤ : Subgroup PUnit))
  exact QuotientGroup.subsingleton_quotient_top

/-- The bottom quotient remains a singleton for a singleton profinite group,
at any universe. -/
theorem subsingleton_bottom_quotient (G : ProfiniteGrp.{u}) [Subsingleton G] :
    Subsingleton (G.closedNormalQuotient
      ⟨⊥, by
        change IsClosed ({1} : Set G)
        exact isClosed_singleton⟩ inferInstance) := by
  change Subsingleton (G ⧸ (⊥ : Subgroup G))
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (⊥ : Subgroup G) x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (⊥ : Subgroup G) y
  exact congrArg (fun element : G ↦ (QuotientGroup.mk element : G ⧸ (⊥ : Subgroup G)))
    (Subsingleton.elim a b)

end ClosedQuotientTests
