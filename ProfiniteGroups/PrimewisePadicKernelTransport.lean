/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicBaseMap
public import ProfiniteGroups.PrimewisePadicIdealTransport

/-!
# Universe transport for primewise p-adic kernels

The coordinate-preserving continuous change of universe on the primewise
group agrees with the coordinate-preserving ring equivalence. Consequently,
precomposition transports kernel ideals by comap and preserves their exponent
families, even for maps that are not surjective. The fixed-source map of any
element has the same exponent family as its original universe-dependent map.

## References

- Mathlib, `ULift.down_injective` and ideal/kernel transport; the preceding
  `PrimewisePadicIdealTransport` and `ProcyclicBaseMap` supply the factor maps.
-/

@[expose] public section

universe u v w

namespace ProfiniteGrp

/-- The continuous group universe change agrees with the algebraic ring
universe change under the multiplicative identifications. -/
theorem primewisePadicChangeUniverse_ringMultiplicativeEquiv
    (x : primewisePadicRing.{u}) :
    primewisePadicChangeUniverse.{u,v}
      (primewisePadicRingMultiplicativeEquiv.{u} (Multiplicative.ofAdd x)) =
    primewisePadicRingMultiplicativeEquiv.{v}
      (Multiplicative.ofAdd (primewisePadicRingChangeUniverse.{u,v} x)) := by
  funext p
  apply Multiplicative.toAdd.injective
  apply ULift.down_injective
  rfl

/-- Precomposition by universe change pulls back the actual kernel ideal,
without any surjectivity or generator hypothesis. -/
theorem primewisePadicKernelIdeal_comp_changeUniverse
    {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{v} →ₜ* Y) :
    primewisePadicKernelIdeal
      (f.comp (primewisePadicChangeUniverse.{u,v} :
        primewisePadic.{u} →ₜ* primewisePadic.{v})) =
      (primewisePadicKernelIdeal f).comap primewisePadicRingChangeUniverse.{u,v} := by
  ext x
  simp only [mem_primewisePadicKernelIdeal, Ideal.mem_comap,
    ContinuousMonoidHom.coe_comp, Function.comp_apply]
  exact Iff.of_eq (congrArg (fun y : primewisePadic.{v} ↦ f y = 1)
    (primewisePadicChangeUniverse_ringMultiplicativeEquiv.{u,v} x))

/-- The coordinate exponents of the actual kernel are independent of the
universe used for the primewise p-adic source. -/
theorem primewisePadicKernelExponents_comp_changeUniverse
    {Y : Type w} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{v} →ₜ* Y) :
    primewisePadicKernelExponents
      (f.comp (primewisePadicChangeUniverse.{u,v} :
        primewisePadic.{u} →ₜ* primewisePadic.{v})) =
      primewisePadicKernelExponents f := by
  unfold primewisePadicKernelExponents
  rw [primewisePadicKernelIdeal_comp_changeUniverse,
    primewisePadicIdealExponents_comap_changeUniverse]

/-- The fixed-source map associated to any element, including a
non-generator, computes the same exponents as the original map. -/
theorem primewisePadicKernelExponents_baseMapOfGenerator
    (G : ProfiniteGrp.{u}) (g : G) :
    primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G g) =
      primewisePadicExponentsOfGenerator G g := by
  exact primewisePadicKernelExponents_comp_changeUniverse.{0,u,u}
    (primewisePadicMapOfGenerator G g)

end ProfiniteGrp
