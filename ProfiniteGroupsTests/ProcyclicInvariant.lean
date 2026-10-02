/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicInvariant

/-!
# Procyclic invariant clients

Proof-using clients for the generator-independent invariant, its fixed-base
model, and the procyclic-only equivalence criterion. Run directly and with
`-T0`, and compare against a fresh root-import client.
-/

@[expose] public section

open ProfiniteGrp

universe u v w

namespace ProcyclicInvariantTests

theorem arbitraryGenerators (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g h : G)
    (hg : IsTopologicalGenerator G g)
    (hh : IsTopologicalGenerator G h) :
    primewisePadicExponentsOfGenerator G g =
      primewisePadicExponentsOfGenerator G h :=
  (hG.exponents_eq_of_generator g hg).symm.trans
    (hG.exponents_eq_of_generator h hh)

theorem independentProofs (G : ProfiniteGrp.{u})
    (hG hG' : IsProcyclic G) : hG.exponents = hG'.exponents :=
  hG.exponents_eq hG'

theorem fixedBase (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (g : G) (hg : IsTopologicalGenerator G g) :
    hG.exponents =
      primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G g) :=
  hG.exponents_eq_baseMap_of_generator g hg

/-- The generator-independent primewise quotient model of a procyclic group. -/
noncomputable def model (G : ProfiniteGrp.{u}) (hG : IsProcyclic G) :
    G ≃ₜ* Multiplicative (primewisePadicQuotientModel.{0} hG.exponents) :=
  hG.continuousMulEquivModel

theorem forward (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (hH : IsProcyclic H) (e : G ≃ₜ* H) :
    hG.exponents = hH.exponents :=
  (isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq G H hG hH).mp ⟨e⟩

theorem backward (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (hH : IsProcyclic H)
    (heq : hG.exponents = hH.exponents) : Nonempty (G ≃ₜ* H) :=
  (isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq G H hG hH).mpr heq

theorem positiveUniverseEquiv (G : ProfiniteGrp.{1})
    (H : ProfiniteGrp.{2}) (hG : IsProcyclic G)
    (hH : IsProcyclic H) (e : G ≃ₜ* H) :
    hG.exponents = hH.exponents :=
  hG.exponents_equiv hH e

theorem independentKernel
    {Y : Type u} {Z : Type v}
    [Group Y] [TopologicalSpace Y] [T1Space Y]
    [Group Z] [TopologicalSpace Z] [T1Space Z]
    (f : primewisePadic.{w} →ₜ* Y) (j : Y →ₜ* Z)
    (hj : Function.Injective j) :
    primewisePadicKernelIdeal (j.comp f) = primewisePadicKernelIdeal f :=
  primewisePadicKernelIdeal_comp_injective f j hj

theorem subsingletonZero (G : ProfiniteGrp.{u})
    [Subsingleton G] (hG : IsProcyclic G) (p : Nat.Primes) :
    hG.exponents p = 0 := by
  have htrivial : primewisePadicBaseMapOfGenerator G (1 : G) = 1 := by
    apply ContinuousMonoidHom.ext
    intro x
    exact Subsingleton.elim _ _
  rw [hG.exponents_eq_baseMap_of_generator 1
    (isTopologicalGenerator_of_subsingleton G 1)]
  exact (primewisePadic_eq_one_iff_kernelExponents_eq_zero _).mp htrivial p

theorem baseMapPrimewiseGenerator :
    primewisePadicBaseMapOfGenerator primewisePadic.{u}
      primewisePadicGenerator =
        (primewisePadicChangeUniverse.{0,u} :
          primewisePadic.{0} →ₜ* primewisePadic.{u}) := by
  apply ContinuousMonoidHom.ext
  have equality := (denseRange_primewisePadicDiagonal.{0}).equalizer
    (primewisePadicBaseMapOfGenerator primewisePadic.{u}
      primewisePadicGenerator).continuous_toFun
    (primewisePadicChangeUniverse.{0,u} :
      primewisePadic.{0} →ₜ* primewisePadic.{u}).continuous_toFun
    (by
      funext n
      change primewisePadicBaseMapOfGenerator primewisePadic.{u}
          primewisePadicGenerator (primewisePadicDiagonal n) =
        primewisePadicChangeUniverse.{0,u} (primewisePadicDiagonal n)
      rw [primewisePadicBaseMapOfGenerator_diagonal,
        primewisePadicChangeUniverse_diagonal]
      funext p
      simpa only [primewisePadicDiagonal_apply] using
        (primewisePadicGenerator_zpow n p))
  exact congrFun equality

theorem primewiseTop (p : Nat.Primes) :
    primewisePadic_isProcyclic.{u}.exponents p = ⊤ := by
  rw [primewisePadic_isProcyclic.{u}.exponents_eq_baseMap_of_generator
    primewisePadicGenerator primewisePadicGenerator_isTopologicalGenerator,
    baseMapPrimewiseGenerator]
  exact (primewisePadic_injective_iff_kernelExponents_eq_top _).mp
    primewisePadicChangeUniverse.{0,u}.injective p

theorem cyclicTwelveCompatibility :
    (finiteCyclic_isProcyclic 12).exponents =
      primewisePadicExponentsOfGenerator (finiteCyclic 12)
        (finiteCyclicGenerator 12) :=
  (finiteCyclic_isProcyclic 12).exponents_eq_of_generator
    (finiteCyclicGenerator 12) (finiteCyclicGenerator_isTopologicalGenerator 12)

theorem cyclicTwoNontrivial :
    (finiteCyclicGenerator 2 : finiteCyclic 2) ≠ 1 := by
  intro heq
  exact (by decide : (1 : ZMod 2) ≠ 0) (congrArg Multiplicative.toAdd heq)

theorem cyclicTwoExponentsNonzero :
    (finiteCyclic_isProcyclic 2).exponents ≠ (fun _ => 0) := by
  intro hall
  have hzero : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator (finiteCyclic 2)
        (finiteCyclicGenerator 2)) p = 0 := by
    intro p
    rw [← (finiteCyclic_isProcyclic 2).exponents_eq_baseMap_of_generator
      (finiteCyclicGenerator 2) (finiteCyclicGenerator_isTopologicalGenerator 2)]
    exact congrFun hall p
  have htrivial : primewisePadicBaseMapOfGenerator (finiteCyclic 2)
      (finiteCyclicGenerator 2) = 1 :=
    (primewisePadic_eq_one_iff_kernelExponents_eq_zero _).mpr hzero
  have hpoint := congrArg (fun f : primewisePadic.{0} →ₜ* finiteCyclic 2 =>
    f (primewisePadicDiagonal 1)) htrivial
  have hone : (finiteCyclicGenerator 2 : finiteCyclic 2) = 1 := by
    simpa [primewisePadicBaseMapOfGenerator_diagonal] using hpoint
  exact cyclicTwoNontrivial hone

theorem cyclicTwoNotEquivalentToSingleton :
    ¬ Nonempty (finiteCyclic 2 ≃ₜ* finiteCyclic 1) := by
  have sub : Subsingleton (finiteCyclic 1) := by
    change Subsingleton (Multiplicative (ZMod 1))
    infer_instance
  intro equiv
  have hexp := (isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq
    (finiteCyclic 2) (finiteCyclic 1)
    (finiteCyclic_isProcyclic 2) (finiteCyclic_isProcyclic 1)).mp equiv
  apply cyclicTwoExponentsNonzero
  apply funext
  intro p
  exact (congrFun hexp p).trans
    (@subsingletonZero (finiteCyclic 1) sub (finiteCyclic_isProcyclic 1) p)

theorem primewiseNotEquivalentToSingleton :
    ¬ Nonempty (primewisePadic.{2} ≃ₜ*
      ofFiniteGrp (FiniteGrp.of PUnit.{2})) := by
  intro equiv
  have hexp := (isProcyclic_nonempty_continuousMulEquiv_iff_exponents_eq
    primewisePadic.{2} (ofFiniteGrp (FiniteGrp.of PUnit.{2}))
    primewisePadic_isProcyclic punit_isProcyclic).mp equiv
  let two : Nat.Primes := ⟨2, by decide⟩
  have heq := congrFun hexp two
  have htop : primewisePadic_isProcyclic.{2}.exponents two = ⊤ := primewiseTop two
  have sub : Subsingleton (ofFiniteGrp (FiniteGrp.of PUnit.{2})) := by
    change Subsingleton PUnit.{2}
    infer_instance
  have hzero : punit_isProcyclic.exponents two = 0 :=
    @subsingletonZero (ofFiniteGrp (FiniteGrp.of PUnit.{2})) sub
      punit_isProcyclic two
  exact (by decide : (⊤ : ℕ∞) ≠ 0) (htop.symm.trans (heq.trans hzero))

end ProcyclicInvariantTests
