/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicQuotient

/-!
# Generator-independent kernels of dense cyclic quotients

Surjective continuous additive maps from a topological ring with dense integer
casts to the same Hausdorff additive group have equal kernels. In particular,
surjective maps from the primewise p-adic product have the same kernel ideal.
Consequently the kernel ideal and its exponents do not depend on the choice of
topological generator of a profinite group.

This generator-independent invariant requires a supplied procyclicity
statement; maps attached to arbitrary individual elements are not promoted
to generator-independent invariants.
-/

@[expose] public section

open Function

universe u v

namespace AddMonoidHom

/-- Two continuous surjective additive maps from a topological ring with dense
integer casts to the same Hausdorff additive group have identical kernels.
Neither ring commutativity nor a topological group structure on the target is
required. The maps themselves need not be equal. -/
theorem ker_eq_of_surjective_dense_intCast
    {R : Type u} {A : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddGroup A] [TopologicalSpace A] [T2Space A]
    (dense : DenseRange (fun n : ℤ => (n : R)))
    (f h : R →+ A) (cf : Continuous f) (ch : Continuous h)
    (sf : Surjective f) (sh : Surjective h) : f.ker = h.ker := by
  have inclusion (p q : R →+ A) (cp : Continuous p) (cq : Continuous q)
      (sp : Surjective p) : p.ker ≤ q.ker := by
    have closed : IsClosed ((p.ker : AddSubgroup R) : Set R) := by
      change IsClosed (p ⁻¹' {0})
      exact isClosed_singleton.preimage cp
    let ideal := p.ker.toIdealOfIsClosedOfDenseIntCast closed dense
    obtain ⟨a, ha⟩ := sp (q 1)
    have on_cast (n : ℤ) : q (n : R) = p (a * (n : R)) := by
      calc
        q (n : R) = q (n • (1 : R)) := by rw [zsmul_one]
        _ = n • q (1 : R) := map_zsmul q n 1
        _ = n • p a := by rw [ha]
        _ = p (n • a) := (map_zsmul p n a).symm
        _ = p (a * (n : R)) := by
          congr 1
          simpa only [zsmul_eq_mul] using (Int.cast_commute n a).eq
    have equality : q = fun x : R => p (a * x) :=
      dense.equalizer cq (cp.comp (continuous_const_mul a)) (by
        funext n
        exact on_cast n)
    intro x hx
    have hx_ideal : x ∈ ideal := hx
    have hax : a * x ∈ ideal := ideal.smul_mem a hx_ideal
    change p (a * x) = 0 at hax
    change q x = 0
    rw [congrFun equality x]
    exact hax
  exact le_antisymm (inclusion f h cf ch sf) (inclusion h f ch cf sh)

end AddMonoidHom

namespace ProfiniteGrp

/-- Continuous surjections from the primewise p-adic product onto the same
Hausdorff group have equal kernel ideals; the maps need not coincide. -/
theorem primewisePadicKernelIdeal_eq_of_surjective
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T2Space Y]
    (f h : primewisePadic.{u} →ₜ* Y)
    (sf : Surjective f) (sh : Surjective h) :
    primewisePadicKernelIdeal f = primewisePadicKernelIdeal h := by
  have additive_t2 : T2Space (Additive Y) :=
    (Homeomorph.mk Additive.ofMul continuous_ofMul continuous_toMul).t2Space
  have continuous_map (p : primewisePadic.{u} →ₜ* Y) :
      Continuous (primewisePadicAdditiveMap p) := by
    change Continuous (Additive.ofMul ∘ p ∘
      primewisePadicRingMultiplicativeEquiv.{u} ∘ Multiplicative.ofAdd)
    exact continuous_ofMul.comp (p.continuous_toFun.comp
      (primewisePadicRingMultiplicativeEquiv.continuous_toFun.comp continuous_ofAdd))
  have surjective_map (p : primewisePadic.{u} →ₜ* Y) (hp : Surjective p) :
      Surjective (primewisePadicAdditiveMap p) := by
    intro y
    obtain ⟨x, hx⟩ := hp (Additive.toMul y)
    refine ⟨(primewisePadicRingMultiplicativeEquiv.{u}.symm x).toAdd, ?_⟩
    simpa [primewisePadicAdditiveMap] using congrArg Additive.ofMul hx
  have kernels := @AddMonoidHom.ker_eq_of_surjective_dense_intCast
    primewisePadicRing.{u} (Additive Y) _ _ _ _ _ additive_t2
    denseRange_intCast_primewisePadicRing
    (primewisePadicAdditiveMap f) (primewisePadicAdditiveMap h)
    (continuous_map f) (continuous_map h)
    (surjective_map f sf) (surjective_map h sh)
  rw [← primewisePadicKernelIdeal_toAddSubgroup f,
    ← primewisePadicKernelIdeal_toAddSubgroup h] at kernels
  exact Ideal.ext (fun x => SetLike.ext_iff.mp kernels x)

/-- The kernel ideal of the primewise map determined by a topological
generator is independent of which topological generator is supplied. -/
theorem primewisePadicKernelIdeal_mapOfGenerator_eq
    (G : ProfiniteGrp.{u}) (g h : G)
    (hg : IsTopologicalGenerator G g) (hh : IsTopologicalGenerator G h) :
    primewisePadicKernelIdeal (primewisePadicMapOfGenerator G g) =
      primewisePadicKernelIdeal (primewisePadicMapOfGenerator G h) :=
  primewisePadicKernelIdeal_eq_of_surjective
    (primewisePadicMapOfGenerator G g) (primewisePadicMapOfGenerator G h)
    (primewisePadicMapOfGenerator_surjective G g hg)
    (primewisePadicMapOfGenerator_surjective G h hh)

/-- The primewise exponent family of a procyclic profinite group is
independent of its supplied topological generator. -/
theorem primewisePadicExponentsOfGenerator_eq
    (G : ProfiniteGrp.{u}) (g h : G)
    (hg : IsTopologicalGenerator G g) (hh : IsTopologicalGenerator G h) :
    primewisePadicExponentsOfGenerator G g =
      primewisePadicExponentsOfGenerator G h := by
  exact congrArg primewisePadicIdealExponents
    (primewisePadicKernelIdeal_mapOfGenerator_eq G g h hg hh)

end ProfiniteGrp
