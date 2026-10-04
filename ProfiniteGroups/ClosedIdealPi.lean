/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Topology.Constructions

/-!
# Closed ideals in product semirings

An ideal of an infinite product need not be the product of its coordinate
images: the finitely supported elements give a standard counterexample.  This
file proves that closed ideals do have the expected coordinatewise form.

## References

- Mathlib, `Mathlib.RingTheory.Ideal.Maps` and `Mathlib.Topology.Constructions` (coordinate
  ideal maps and product topology).
-/

@[expose] public section

open Filter

universe u v

namespace Ideal

/-- A closed ideal in a product of topological semirings is the product of its
coordinate images.

No compatibility between the topology and the semiring operations, and no
separation, compactness, or nonemptiness assumption, is needed.

Uses Mathlib’s `Ideal.pi`, coordinate ideal maps and product topology; no printed procyclic
theorem is asserted for this general product-ideal result. -/
theorem eq_pi_map_evalRingHom_of_isClosed
    {ι : Type u} {R : ι → Type v} [∀ i, Semiring (R i)]
    [∀ i, TopologicalSpace (R i)] (I : Ideal (∀ i, R i))
    (hI : IsClosed (I : Set (∀ i, R i))) :
    I = Ideal.pi (fun i ↦ I.map (Pi.evalRingHom R i)) := by
  ext x
  rw [mem_pi]
  constructor
  · intro hx i
    exact mem_map_of_mem (Pi.evalRingHom R i) hx
  · intro hx
    have hlift (i : ι) : ∃ y : ∀ i, R i, y ∈ I ∧ y i = x i := by
      simpa only [mem_map_iff_of_surjective (Pi.evalRingHom R i)
        (Function.surjective_eval i), Pi.evalRingHom_apply] using hx i
    choose y hyI hy using hlift
    classical
    let trunc : Finset ι → (∀ i, R i) := fun s ↦
      ∑ i ∈ s, Pi.single i 1 * y i
    apply hI.mem_of_tendsto (f := trunc) (b := atTop)
    · apply tendsto_pi_nhds.2
      intro i
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [eventually_finset_mem_atTop i] with s his
      simp only [trunc, Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · simpa using hy i
      · intro j _ hji
        simp [Pi.single_eq_of_ne hji.symm]
      · simp [his]
    · exact Eventually.of_forall fun s ↦
        I.sum_mem fun i _ ↦ I.mul_mem_left (Pi.single i 1) (hyI i)

end Ideal
