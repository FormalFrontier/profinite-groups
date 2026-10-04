/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.PrimewisePadic

/-!
# Closed kernels in the primewise p-adic product

This file exposes the product ring underlying `ProfiniteGrp.primewisePadic` and
turns the kernel of any continuous multiplicative homomorphism out of that
group into an ideal of the product ring.

The generic bridge used here applies to any topological ring whose integer
casts are dense: every closed additive subgroup is then a left ideal.  No
commutativity or surjectivity assumption is needed.

## References

- Mathlib, `Mathlib.NumberTheory.Padics.RingHoms`, `MonoidHom.ker` and
  closed-subgroup constructions (coordinate kernels of the primewise product).
-/

@[expose] public section

open Function Set

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The product ring underlying the primewise p-adic profinite group. -/
abbrev primewisePadicRing :=
  (p : Nat.Primes) → ULift.{u} ℤ_[p.1]

/-- The coordinatewise continuous multiplicative equivalence from the
primewise p-adic product ring, written multiplicatively, to
`primewisePadic`. -/
noncomputable def primewisePadicRingMultiplicativeEquiv :
    Multiplicative primewisePadicRing.{u} ≃ₜ* primewisePadic.{u} := by
  change Multiplicative ((p : Nat.Primes) → ULift.{u} ℤ_[p.1]) ≃ₜ*
    ((p : Nat.Primes) → Multiplicative (ULift.{u} ℤ_[p.1]))
  exact
    { MulEquiv.piMultiplicative (fun p : Nat.Primes ↦ ULift.{u} ℤ_[p.1]) with
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

/-- Integer casts are dense in the product ring underlying
`primewisePadic`. -/
theorem denseRange_intCast_primewisePadicRing :
    DenseRange (fun n : ℤ ↦ (n : primewisePadicRing.{u})) := by
  change DenseRange (fun n : ℤ ↦
    Multiplicative.ofAdd (n : primewisePadicRing.{u}))
  have h :=
    primewisePadicRingMultiplicativeEquiv.{u}.symm.surjective.denseRange.comp
      denseRange_primewisePadicDiagonal
      primewisePadicRingMultiplicativeEquiv.{u}.symm.continuous_toFun
  convert h using 1
  funext n
  apply Multiplicative.toAdd.injective
  funext p
  rfl

end ProfiniteGrp

namespace AddSubgroup

/-- A closed additive subgroup of a topological ring with dense integer casts
is a left ideal.

For `k ∈ K`, the set of `r` such that `r * k ∈ K` is closed and contains
every integer cast.  Density therefore makes this set the whole ring. -/
def toIdealOfIsClosedOfDenseIntCast
    {R : Type u} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (K : AddSubgroup R) (hK : IsClosed (K : Set R))
    (hℤ : DenseRange (fun n : ℤ ↦ (n : R))) : Ideal R where
  carrier := K
  zero_mem' := K.zero_mem
  add_mem' := K.add_mem
  smul_mem' := by
    intro r k hk
    change r * k ∈ K
    let S : Set R := {a | a * k ∈ K}
    have hS : IsClosed S := hK.preimage (continuous_mul_const k)
    have hrange : range (fun n : ℤ ↦ (n : R)) ⊆ S := by
      rintro _ ⟨n, rfl⟩
      change (n : R) * k ∈ K
      simpa only [← zsmul_eq_mul] using K.zsmul_mem hk n
    have huniv : (univ : Set R) ⊆ S := by
      rw [← hℤ.closure_range]
      exact closure_minimal hrange hS
    exact huniv (mem_univ r)

/-- Membership in the ideal obtained from a closed additive subgroup is
unchanged. -/
@[simp]
theorem mem_toIdealOfIsClosedOfDenseIntCast
    {R : Type u} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (K : AddSubgroup R) (hK : IsClosed (K : Set R))
    (hℤ : DenseRange (fun n : ℤ ↦ (n : R))) (x : R) :
    x ∈ K.toIdealOfIsClosedOfDenseIntCast hK hℤ ↔ x ∈ K :=
  Iff.rfl

end AddSubgroup

namespace ProfiniteGrp

/-- The kernel of a continuous multiplicative homomorphism out of the
primewise p-adic group, regarded as an ideal of its underlying product ring.

Uses Mathlib’s kernel, closed-subgroup and p-adic product APIs; this general ideal
construction is not attributed to a printed procyclic theorem. -/
noncomputable def primewisePadicKernelIdeal
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) : Ideal primewisePadicRing.{u} := by
  let φ : Multiplicative primewisePadicRing.{u} →ₜ* Y :=
    f.comp (primewisePadicRingMultiplicativeEquiv :
      Multiplicative primewisePadicRing.{u} →ₜ* primewisePadic.{u})
  let K : AddSubgroup primewisePadicRing.{u} :=
    φ.toMonoidHom.ker.toAddSubgroup'
  apply K.toIdealOfIsClosedOfDenseIntCast
  · change IsClosed ((fun x : primewisePadicRing.{u} ↦
        φ (Multiplicative.ofAdd x)) ⁻¹' {1})
    exact isClosed_singleton.preimage
      (φ.continuous_toFun.comp continuous_ofAdd)
  · exact denseRange_intCast_primewisePadicRing

/-- Membership in the primewise p-adic kernel ideal is exactly vanishing
under the original multiplicative homomorphism. -/
@[simp]
theorem mem_primewisePadicKernelIdeal
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) (x : primewisePadicRing.{u}) :
    x ∈ primewisePadicKernelIdeal f ↔
      f (primewisePadicRingMultiplicativeEquiv
        (Multiplicative.ofAdd x)) = 1 := by
  simp [primewisePadicKernelIdeal]

/-- The carrier of the primewise p-adic kernel ideal is closed. -/
theorem isClosed_primewisePadicKernelIdeal
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) :
    IsClosed ((primewisePadicKernelIdeal f :
      Ideal primewisePadicRing.{u}) : Set primewisePadicRing.{u}) := by
  unfold primewisePadicKernelIdeal
  dsimp only
  change IsClosed ((fun x : primewisePadicRing.{u} ↦
    f (primewisePadicRingMultiplicativeEquiv
      (Multiplicative.ofAdd x))) ⁻¹' {1})
  exact isClosed_singleton.preimage
    (f.continuous_toFun.comp
      (primewisePadicRingMultiplicativeEquiv.continuous_toFun.comp
        continuous_ofAdd))

end ProfiniteGrp
