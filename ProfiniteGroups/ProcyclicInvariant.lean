/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicGeneratorIndependence
public import ProfiniteGroups.PrimewisePadicKernelTransport

/-!
# Invariants and classification of procyclic profinite groups

A proof that a profinite group is procyclic determines a generator-independent
family of primewise p-adic kernel exponents. The family agrees with the
previous generator-dependent exponents for every actual generator. Two
procyclic profinite groups, even in different universes, are continuously
multiplicatively equivalent exactly when their exponent families agree.

The family is defined from a chosen witness but proved independent of that
choice. The equivalence assumes both groups are procyclic; an arbitrary
target need not carry such an invariant.
-/

@[expose] public section

universe u v w

namespace ProfiniteGrp

/-- Postcomposition by an injective continuous homomorphism preserves the
actual primewise p-adic kernel ideal, with no surjectivity assumption. -/
theorem primewisePadicKernelIdeal_comp_injective
    {Y : Type v} {Z : Type w}
    [Group Y] [TopologicalSpace Y] [T1Space Y]
    [Group Z] [TopologicalSpace Z] [T1Space Z]
    (f : primewisePadic.{u} →ₜ* Y) (j : Y →ₜ* Z)
    (hj : Function.Injective j) :
    primewisePadicKernelIdeal (j.comp f) = primewisePadicKernelIdeal f := by
  ext x
  simp only [mem_primewisePadicKernelIdeal, ContinuousMonoidHom.coe_comp,
    Function.comp_apply, ← map_one j]
  exact hj.eq_iff

namespace IsProcyclic

/-- The primewise exponents of a procyclic profinite group, formed using a
chosen generator and the fixed universe-zero p-adic source. Independent of
the chosen generator by `exponents_eq_of_generator`. -/
noncomputable def exponents {G : ProfiniteGrp.{u}} (hG : IsProcyclic G) :
    Nat.Primes → ℕ∞ :=
  primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G hG.choose)

/-- The fixed-base exponent family does not depend on the supplied
topological generator. -/
theorem baseMap_exponents_eq_of_generators
    (G : ProfiniteGrp.{u}) (g h : G)
    (hg : IsTopologicalGenerator G g) (hh : IsTopologicalGenerator G h) :
    primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G g) =
      primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G h) := by
  exact congrArg primewisePadicIdealExponents
    (primewisePadicKernelIdeal_eq_of_surjective
      (primewisePadicBaseMapOfGenerator G g)
      (primewisePadicBaseMapOfGenerator G h)
      (primewisePadicBaseMapOfGenerator_surjective G g hg)
      (primewisePadicBaseMapOfGenerator_surjective G h hh))

/-- The invariant agrees with the fixed-base kernel exponent family for
any actual topological generator. -/
theorem exponents_eq_baseMap_of_generator
    {G : ProfiniteGrp.{u}} (hG : IsProcyclic G) (g : G)
    (hg : IsTopologicalGenerator G g) :
    hG.exponents =
      primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G g) :=
  baseMap_exponents_eq_of_generators G hG.choose g hG.choose_spec hg

/-- Any supplied generator computes the invariant using the original
generator-dependent exponent family. -/
theorem exponents_eq_of_generator
    {G : ProfiniteGrp.{u}} (hG : IsProcyclic G) (g : G)
    (hg : IsTopologicalGenerator G g) :
    hG.exponents = primewisePadicExponentsOfGenerator G g := by
  rw [hG.exponents_eq_baseMap_of_generator g hg,
    primewisePadicKernelExponents_baseMapOfGenerator]

/-- The exponent family is independent of the proof of procyclicity. -/
theorem exponents_eq
    {G : ProfiniteGrp.{u}} (hG hG' : IsProcyclic G) :
    hG.exponents = hG'.exponents := by
  exact (hG.exponents_eq_of_generator hG.choose hG.choose_spec).trans
    (hG'.exponents_eq_of_generator hG.choose hG.choose_spec).symm

/-- An equivalence of procyclic profinite groups preserves their exponents,
even when the groups live in different universes. -/
theorem exponents_equiv
    {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (hH : IsProcyclic H) (e : G ≃ₜ* H) :
    hG.exponents = hH.exponents := by
  let g : G := hG.choose
  have hg : IsTopologicalGenerator G g := hG.choose_spec
  have hehg : IsTopologicalGenerator H (e g) := hg.map_equiv e
  have hmap := primewisePadicBaseMapOfGenerator_naturality G H
    (e : G →ₜ* H) g
  have hker : primewisePadicKernelIdeal
      (primewisePadicBaseMapOfGenerator H (e g)) =
      primewisePadicKernelIdeal (primewisePadicBaseMapOfGenerator G g) := by
    exact (congrArg (fun f : primewisePadic.{0} →ₜ* H =>
      primewisePadicKernelIdeal f) hmap).symm.trans
        (primewisePadicKernelIdeal_comp_injective
          (primewisePadicBaseMapOfGenerator G g) (e : G →ₜ* H) e.injective)
  calc
    hG.exponents =
        primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G g) :=
      hG.exponents_eq_baseMap_of_generator g hg
    _ = primewisePadicKernelExponents
        (primewisePadicBaseMapOfGenerator H (e g)) :=
      congrArg primewisePadicIdealExponents hker.symm
    _ = hH.exponents :=
      (hH.exponents_eq_baseMap_of_generator (e g) hehg).symm

/-- A procyclic group is modeled by the quotient product for its
generator-independent exponents. The equivalence is noncomputable because
selecting a generator and constructing the quotient model use choice. -/
noncomputable def continuousMulEquivModel
    {G : ProfiniteGrp.{u}} (hG : IsProcyclic G) :
    G ≃ₜ* Multiplicative (primewisePadicQuotientModel.{0} hG.exponents) :=
  primewisePadicContinuousMulEquivModel
    (primewisePadicBaseMapOfGenerator G hG.choose)
    (primewisePadicBaseMapOfGenerator_surjective G hG.choose hG.choose_spec)

end IsProcyclic

/-- Two already-procyclic profinite groups, in possibly different universes,
are topologically multiplicatively equivalent if and only if their
generator-independent exponent families coincide. -/
theorem isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq
    (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (hH : IsProcyclic H) :
    Nonempty (G ≃ₜ* H) ↔ hG.exponents = hH.exponents := by
  constructor
  · rintro ⟨e⟩
    exact hG.exponents_equiv hH e
  · intro heq
    have eG : G ≃ₜ* Multiplicative
        (primewisePadicQuotientModel.{0} hH.exponents) := by
      exact Eq.mp (congrArg (fun exponents : Nat.Primes → ℕ∞ =>
        G ≃ₜ* Multiplicative (primewisePadicQuotientModel.{0} exponents)) heq)
        hG.continuousMulEquivModel
    exact ⟨eG.trans hH.continuousMulEquivModel.symm⟩

end ProfiniteGrp
