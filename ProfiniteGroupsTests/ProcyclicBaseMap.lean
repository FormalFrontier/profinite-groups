/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicBaseMap

/-!
# Procyclic base-map clients

Direct-import clients for the primewise change of universe and common-source
generator maps. Run in ordinary and `-T0` modes.
-/

@[expose] public section

open ProfiniteGrp

universe u v w

namespace ProcyclicBaseMapTests

section UniverseChange

/-- The composition law preserves coordinates in three independent universes. -/
theorem transCoordinates (x : primewisePadic.{u}) (p : Nat.Primes) :
    (((primewisePadicChangeUniverse.{u,v}.trans
        primewisePadicChangeUniverse.{v,w}) x) p).toAdd.down =
      (x p).toAdd.down := by
  rw [primewisePadicChangeUniverse_trans,
    primewisePadicChangeUniverse_apply_down]

example (x : primewisePadic.{u}) (p : Nat.Primes) :
    ((primewisePadicChangeUniverse.{u,v} x) p).toAdd.down =
      (x p).toAdd.down :=
  primewisePadicChangeUniverse_apply_down.{u,v} x p

example (n : ℤ) :
    primewisePadicChangeUniverse.{u,v} (primewisePadicDiagonal.{u} n) =
      primewisePadicDiagonal.{v} n := by simp

example : primewisePadicChangeUniverse.{u,u} = ContinuousMulEquiv.refl _ := by simp

example : primewisePadicChangeUniverse.{u,v}.symm =
    primewisePadicChangeUniverse.{v,u} := by simp

example : primewisePadicChangeUniverse.{u,v}.trans
    primewisePadicChangeUniverse.{v,w} =
      primewisePadicChangeUniverse.{u,w} := by simp

example : primewisePadicChangeUniverse.{u,v} primewisePadicGenerator =
    primewisePadicGenerator := by simp

example (x : primewisePadic.{0}) (p : Nat.Primes) :
    ((primewisePadicChangeUniverse.{0,u} x) p).toAdd.down =
      (x p).toAdd.down := by simp

example (x : primewisePadic.{u}) (p : Nat.Primes) :
    ((primewisePadicChangeUniverse.{u,0} x) p).toAdd.down =
      (x p).toAdd.down := by simp

end UniverseChange

section CommonSource

example (G : ProfiniteGrp.{u}) (g : G) (n : ℤ) :
    primewisePadicBaseMapOfGenerator G g (primewisePadicDiagonal.{0} n) =
      g ^ n := by simp

example (G : ProfiniteGrp.{u}) (g : G)
    (hg : IsTopologicalGenerator G g) :
    Function.Surjective (primewisePadicBaseMapOfGenerator G g) :=
  primewisePadicBaseMapOfGenerator_surjective G g hg

example : Function.Surjective (primewisePadicBaseMapOfGenerator
    primewisePadic.{u} primewisePadicGenerator) :=
  primewisePadicBaseMapOfGenerator_surjective _ _
    primewisePadicGenerator_isTopologicalGenerator

example : Function.Surjective (primewisePadicBaseMapOfGenerator
    (finiteCyclic 1) (finiteCyclicGenerator 1)) :=
  primewisePadicBaseMapOfGenerator_surjective _ _
    (finiteCyclicGenerator_isTopologicalGenerator 1)

/-- The finite cyclic group of order twelve has a common-source surjection. -/
theorem finite12Surjective : Function.Surjective (primewisePadicBaseMapOfGenerator
    (finiteCyclic 12) (finiteCyclicGenerator 12)) :=
  primewisePadicBaseMapOfGenerator_surjective _ _
    (finiteCyclicGenerator_isTopologicalGenerator 12)

example (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (f : G →ₜ* H) (g : G) :
    f.comp (primewisePadicBaseMapOfGenerator G g) =
      primewisePadicBaseMapOfGenerator H (f g) :=
  primewisePadicBaseMapOfGenerator_naturality G H f g

/-- Naturality for a continuous equivalence between independent universes. -/
theorem equivNaturality (g : primewisePadic.{u}) :
    (primewisePadicChangeUniverse.{u,v} : primewisePadic.{u} →ₜ*
      primewisePadic.{v}).comp
      (primewisePadicBaseMapOfGenerator primewisePadic.{u} g) =
        primewisePadicBaseMapOfGenerator primewisePadic.{v}
          (primewisePadicChangeUniverse.{u,v} g) :=
  primewisePadicBaseMapOfGenerator_naturality _ _ _ _

example (g : finiteCyclic 12) :
    (1 : finiteCyclic 12 →ₜ* finiteCyclic 12).comp
      (primewisePadicBaseMapOfGenerator (finiteCyclic 12) g) =
        primewisePadicBaseMapOfGenerator (finiteCyclic 12) 1 := by
  simpa using primewisePadicBaseMapOfGenerator_naturality
    (finiteCyclic 12) (finiteCyclic 12)
      (1 : finiteCyclic 12 →ₜ* finiteCyclic 12) g

/-- The finite endomorphism used for naturality is not surjective. -/
theorem finite12ConstantNotSurjective :
    ¬ Function.Surjective (1 : finiteCyclic 12 →ₜ* finiteCyclic 12) := by
  intro hs
  obtain ⟨x, hx⟩ := hs (finiteCyclicGenerator 12)
  have heq : (finiteCyclicGenerator 12 : finiteCyclic 12) = 1 := by
    simpa using hx.symm
  exact (by decide : (1 : ZMod 12) ≠ 0)
    (congrArg Multiplicative.toAdd heq)

example (x : primewisePadic.{0}) :
    primewisePadicBaseMapOfGenerator (finiteCyclic 12)
      (1 : finiteCyclic 12) x = 1 := by
  have h := primewisePadicBaseMapOfGenerator_naturality
    (finiteCyclic 12) (finiteCyclic 12)
      (1 : finiteCyclic 12 →ₜ* finiteCyclic 12)
      (finiteCyclicGenerator 12)
  have hx := congrArg (fun f : primewisePadic.{0} →ₜ* finiteCyclic 12 => f x) h
  simpa using hx.symm

/-- The identity in the nontrivial finite cyclic group is not a generator. -/
theorem finite12OneNotGenerator : ¬ IsTopologicalGenerator (finiteCyclic 12)
    (1 : finiteCyclic 12) := by
  have hne : (finiteCyclicGenerator 12 : finiteCyclic 12) ≠ 1 := by
    intro h
    exact (by decide : (1 : ZMod 12) ≠ 0)
      (congrArg Multiplicative.toAdd h)
  have hconst (x : primewisePadic.{0}) :
      primewisePadicBaseMapOfGenerator (finiteCyclic 12)
        (1 : finiteCyclic 12) x = 1 := by
    have h := primewisePadicBaseMapOfGenerator_naturality
      (finiteCyclic 12) (finiteCyclic 12)
        (1 : finiteCyclic 12 →ₜ* finiteCyclic 12)
        (finiteCyclicGenerator 12)
    have hx := congrArg (fun f : primewisePadic.{0} →ₜ* finiteCyclic 12 => f x) h
    simpa using hx.symm
  intro hg
  obtain ⟨x, hx⟩ := primewisePadicBaseMapOfGenerator_surjective
    (finiteCyclic 12) 1 hg (finiteCyclicGenerator 12)
  exact hne (hx.symm.trans (hconst x))

end CommonSource

end ProcyclicBaseMapTests
