/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.PrimewisePadicSubgroups
public import ProfiniteGroups.ProcyclicBaseMap
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Closed subgroups of procyclic profinite groups

Every closed subgroup, including a non-open one, inherits a topological generator.
The proof first generates an arbitrary closed subgroup of the primewise p-adic
product: a closed ideal of its product ring is a product of principal ideals,
so it is the image of multiplication by one element. The integral diagonal
is dense, and its image gives a topological generator. An arbitrary procyclic
group is a continuous quotient of this fixed product, whose inverse image of
a closed subgroup is closed; restricting the quotient map transports the
generator to the actual closed subgroup.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (primewise description of procyclic groups; the closed-subgroup inheritance proof
  here is a consequence, not a printed theorem).
- Mathlib, `Mathlib.RingTheory.PrincipalIdealDomain` and closed-subgroup constructions;
  `PrimewisePadicSubgroups` and `ProcyclicBaseMap` supply the quotient model.
-/

@[expose] public section

open Set

universe u

namespace ProfiniteGrp

private instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private theorem exists_mul_generator_closed_primewiseIdeal
    (I : Ideal primewisePadicRing.{u})
    (hI : IsClosed (I : Set primewisePadicRing.{u})) :
    ∃ a : primewisePadicRing.{u},
      ∀ x, x ∈ I ↔ ∃ y : primewisePadicRing.{u}, a * y = x := by
  have hPrincipal (p : Nat.Primes) :
      ∃ a : ULift.{u} ℤ_[p.1],
        I.map (Pi.evalRingHom
          (fun q : Nat.Primes ↦ ULift.{u} ℤ_[q.1]) p) = Ideal.span {a} := by
    have hPrincipalRing : IsPrincipalIdealRing (ULift.{u} ℤ_[p.1]) :=
      IsPrincipalIdealRing.of_surjective
        ULift.ringEquiv.symm.toRingHom ULift.ringEquiv.symm.surjective
    exact (hPrincipalRing.principal _).principal
  choose a ha using hPrincipal
  refine ⟨a, fun x ↦ ?_⟩
  rw [Ideal.eq_pi_map_evalRingHom_of_isClosed I hI]
  change (∀ p, x p ∈ I.map (Pi.evalRingHom
    (fun q : Nat.Primes ↦ ULift.{u} ℤ_[q.1]) p)) ↔ ∃ y, a * y = x
  constructor
  · intro hx
    have hy (p : Nat.Primes) : ∃ y : ULift.{u} ℤ_[p.1], a p * y = x p := by
      have hxp := hx p
      rw [ha p, Ideal.mem_span_singleton'] at hxp
      obtain ⟨y, hy⟩ := hxp
      exact ⟨y, by simpa only [mul_comm] using hy⟩
    choose y hy using hy
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩ p
    rw [ha p, Ideal.mem_span_singleton']
    exact ⟨y p, by simp only [Pi.mul_apply, mul_comm]⟩

private theorem exists_surjective_primewiseClosedSubgroupMap
    (H : ClosedSubgroup primewisePadic.{u}) :
    ∃ f : primewisePadic.{u} →ₜ* ofClosedSubgroup H, Function.Surjective f := by
  let K := primewisePadicClosedSubgroupToClosedAddSubgroup H
  let I := primewisePadicClosedAddSubgroupIdeal K
  have hclosed : IsClosed (I : Set primewisePadicRing.{u}) := by
    change IsClosed (K : Set primewisePadicRing.{u})
    exact K.isClosed'
  obtain ⟨a, ha⟩ := exists_mul_generator_closed_primewiseIdeal I hclosed
  let e := primewisePadicRingMultiplicativeEquiv.{u}
  let f : primewisePadic.{u} →ₜ* ofClosedSubgroup H :=
    ⟨{
      toFun := fun x ↦ ⟨e (Multiplicative.ofAdd (a * (e.symm x).toAdd)), by
        have hm : a * (e.symm x).toAdd ∈ I := (ha _).mpr ⟨_, rfl⟩
        exact hm⟩
      map_one' := by
        apply Subtype.ext
        change e (Multiplicative.ofAdd (a * (e.symm (1 : primewisePadic.{u})).toAdd)) = 1
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change e (Multiplicative.ofAdd (a * (e.symm (x * y)).toAdd)) =
          e (Multiplicative.ofAdd (a * (e.symm x).toAdd)) *
          e (Multiplicative.ofAdd (a * (e.symm y).toAdd))
        simp [mul_add]
    }, by
      apply Continuous.subtype_mk
      fun_prop⟩
  refine ⟨f, ?_⟩
  intro x
  have hx : (e.symm x.1).toAdd ∈ I := x.2
  obtain ⟨y, hy⟩ := (ha _).mp hx
  refine ⟨e (Multiplicative.ofAdd y), Subtype.ext ?_⟩
  change e (Multiplicative.ofAdd
    (a * (e.symm (e (Multiplicative.ofAdd y))).toAdd)) = x.1
  simp only [e.symm_apply_apply]
  change e (Multiplicative.ofAdd (a * y)) = x.1
  rw [hy]
  exact e.apply_symm_apply x.1

/-- A closed subgroup of the primewise p-adic product is procyclic in its
inherited profinite group structure. -/
theorem primewisePadicClosedSubgroup_isProcyclic
    (H : ClosedSubgroup primewisePadic.{u}) :
    IsProcyclic (ofClosedSubgroup H) := by
  obtain ⟨f, hf⟩ := exists_surjective_primewiseClosedSubgroupMap H
  exact ⟨f primewisePadicGenerator,
    primewisePadicGenerator_isTopologicalGenerator.map f hf⟩

/-- Every closed subgroup of a procyclic profinite group is procyclic in its
inherited topology and group structure.

This closed-subgroup inheritance is derived from the primewise quotient description in
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
(1.7.7), with Mathlib’s p-adic ideal APIs; it is not quoted there as a separate
theorem. -/
theorem IsProcyclic.ofClosedSubgroup {G : ProfiniteGrp.{u}} (hG : IsProcyclic G)
    (H : ClosedSubgroup G) : IsProcyclic (ofClosedSubgroup H) := by
  obtain ⟨g, hg⟩ := hG
  let f := primewisePadicBaseMapOfGenerator G g
  have hf : Function.Surjective f :=
    primewisePadicBaseMapOfGenerator_surjective G g hg
  let K : ClosedSubgroup primewisePadic.{0} :=
    { toSubgroup := H.toSubgroup.comap f.toMonoidHom
      isClosed' := H.isClosed'.preimage f.continuous_toFun }
  let fK : ProfiniteGrp.ofClosedSubgroup K →ₜ* ProfiniteGrp.ofClosedSubgroup H :=
    ⟨{
      toFun := fun x ↦ ⟨f x.1, x.2⟩
      map_one' := by apply Subtype.ext; exact map_one f
      map_mul' := by intro x y; apply Subtype.ext; exact map_mul f x.1 y.1
    }, (f.continuous_toFun.comp continuous_subtype_val).subtype_mk
      (fun x ↦ x.2)⟩
  have hfK : Function.Surjective fK := by
    intro x
    obtain ⟨y, hy⟩ := hf x.1
    have hyK : y ∈ K := by
      change f y ∈ H
      rw [hy]
      exact x.2
    exact ⟨⟨y, hyK⟩, Subtype.ext hy⟩
  obtain ⟨k, hk⟩ := primewisePadicClosedSubgroup_isProcyclic K
  exact ⟨fK k, hk.map fK hfK⟩

/-- A closed subgroup has a generator inside it whose integral powers are
dense in the inherited topology. -/
theorem IsProcyclic.exists_closedSubgroup_generator
    {G : ProfiniteGrp.{u}} (hG : IsProcyclic G) (H : ClosedSubgroup G) :
    ∃ g : ProfiniteGrp.ofClosedSubgroup H,
      (Subgroup.zpowers g).topologicalClosure = ⊤ := by
  obtain ⟨g, hg⟩ := hG.ofClosedSubgroup H
  exact ⟨g, IsTopologicalGenerator.iff_topologicalClosure_zpowers.mp hg⟩

/-- The closedness witness for an ordinary subgroup suffices for inheritance. -/
theorem IsProcyclic.ofSubgroup_isClosed {G : ProfiniteGrp.{u}}
    (hG : IsProcyclic G) (H : Subgroup G)
    (hH : IsClosed (H : Set G)) :
    IsProcyclic (ProfiniteGrp.ofClosedSubgroup ⟨H, hH⟩) :=
  hG.ofClosedSubgroup ⟨H, hH⟩

end ProfiniteGrp
