/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicPower
public import ProfiniteGroups.ProcyclicHom
public import ProfiniteGroups.ProcyclicTorsionFree
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing

/-!
# Exact indices and finite cyclic quotients of procyclic groups

For a positive integer `n`, the subgroup of `n`-th powers has index `n` exactly
when each prime multiplicity of `n` is bounded by the corresponding exponent of
the procyclic group. The quotient is then continuously isomorphic to the
multiplicative version of `ZMod n`. Supplying a topological generator specifies
which equivalence is meant: the additive class of one maps to its quotient class.

In the torsion-free case, the permissible integers are supported on the primes
with infinite exponent. No torsion-freeness assumption is needed for the general
index criterion or the chosen-generator quotient equivalence.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (torsion-free supported power indices; the arbitrary-procyclic exact-index
  criterion is a refinement).
- Mathlib, `Mathlib.Data.Nat.Factorization.Basic` and `Mathlib.Data.ZMod.QuotientRing`
  (prime multiplicities and cyclic quotient models).
-/

@[expose] public section

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

private noncomputable def residueRingHom (n : ℕ) (hn : n ≠ 0) :
    primewisePadicRing.{u} →+* ZMod n :=
  (ZMod.equivPi n hn).symm.toRingHom.comp
    (RingHom.pi fun q : n.primeFactors ↦
      (liftedPadicToZModPow.{u}
        ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩ (n.factorization q.1)).comp
        (Pi.evalRingHom (fun p : Nat.Primes ↦ ULift.{u} ℤ_[p.1])
          ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩))

private theorem residueRingHom_apply (n : ℕ) (hn : n ≠ 0)
    (x : primewisePadicRing.{u}) (q : n.primeFactors) :
    ZMod.equivPi n hn (residueRingHom n hn x) q =
      liftedPadicToZModPow ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
        (n.factorization q.1) (x ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩) := by
  simp [residueRingHom]
  rfl

private theorem residueRingHom_ker (n : ℕ) (hn : n ≠ 0) :
    RingHom.ker (residueRingHom.{u} n hn) =
      primewisePadicIdealOfExponents (fun p ↦ (n.factorization p.1 : ℕ∞)) := by
  ext x
  rw [RingHom.mem_ker, mem_primewisePadicIdealOfExponents]
  constructor
  · intro hx p
    by_cases hp : p.1 ∈ n.primeFactors
    · let q : n.primeFactors := ⟨p.1, hp⟩
      have hq := congrArg (fun y : ZMod n ↦ ZMod.equivPi n hn y q) hx
      rw [residueRingHom_apply, map_zero, Pi.zero_apply] at hq
      rw [← ker_liftedPadicToZModPow]
      exact RingHom.mem_ker.mpr hq
    · have hz : n.factorization p.1 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd
          (fun hdvd ↦ hp (p.2.mem_primeFactors hdvd hn))
      simp [hz]
  · intro hx
    apply (ZMod.equivPi n hn).injective
    funext q
    rw [map_zero, residueRingHom_apply, Pi.zero_apply]
    let p : Nat.Primes := ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
    have hp : x p ∈ RingHom.ker (liftedPadicToZModPow p (n.factorization p.1)) := by
      rw [ker_liftedPadicToZModPow]
      exact hx p
    exact RingHom.mem_ker.mp hp

private theorem isOpen_residueRingHom_ker (n : ℕ) (hn : n ≠ 0) :
    IsOpen ((RingHom.ker (residueRingHom.{u} n hn) :
      Ideal primewisePadicRing.{u}) : Set primewisePadicRing.{u}) := by
  rw [residueRingHom_ker]
  have heq : ((primewisePadicIdealOfExponents
      (fun p ↦ (n.factorization p.1 : ℕ∞)) : Ideal primewisePadicRing.{u}) :
      Set primewisePadicRing.{u}) =
      ⋂ q : n.primeFactors,
        {x : primewisePadicRing.{u} |
          x ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩ ∈
            liftedPadicIdealOfExponent
              ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
              (n.factorization q.1 : ℕ∞)} := by
    ext x
    simp only [SetLike.mem_coe, mem_primewisePadicIdealOfExponents,
      Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hx q
      exact hx _
    · intro hx p
      by_cases hp : p.1 ∈ n.primeFactors
      · exact hx ⟨p.1, hp⟩
      · have hz : n.factorization p.1 = 0 :=
          Nat.factorization_eq_zero_of_not_dvd
            (fun hdvd ↦ hp (p.2.mem_primeFactors hdvd hn))
        simp [hz]
  rw [heq]
  have hcoordinate (q : n.primeFactors) :
      IsOpen {x : primewisePadicRing.{u} |
        x ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩ ∈
          liftedPadicIdealOfExponent
            ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
            (n.factorization q.1 : ℕ∞)} := by
    let p : Nat.Primes := ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
    change IsOpen ((fun x : primewisePadicRing.{u} ↦ x p) ⁻¹'
      (liftedPadicIdealOfExponent p (n.factorization q.1 : ℕ∞) :
        Set (ULift.{u} ℤ_[p.1])))
    exact (isOpen_liftedPadicIdealOfExponent_natCast p (n.factorization q.1)).preimage
      (continuous_apply p)
  exact isOpen_iInter_of_finite hcoordinate

private theorem continuous_residueRingHom (n : ℕ) (hn : n ≠ 0) :
    Continuous (residueRingHom.{u} n hn) := by
  apply continuous_of_continuousAt_zero (residueRingHom n hn).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  rw [show nhds (0 : ZMod n) = pure (0 : ZMod n) by
    exact congrFun (nhds_discrete (ZMod n)) 0, Filter.tendsto_pure]
  change (RingHom.ker (residueRingHom n hn) : Set primewisePadicRing.{u}) ∈ nhds 0
  exact (isOpen_residueRingHom_ker n hn).mem_nhds (Ideal.zero_mem _)

private noncomputable def residueContinuousMulHom (n : ℕ) [NeZero n] :
    primewisePadic.{u} →ₜ* finiteCyclic n := by
  let f : Multiplicative primewisePadicRing.{u} →ₜ* finiteCyclic n :=
    ⟨(residueRingHom n (NeZero.ne n)).toAddMonoidHom.toMultiplicative,
      continuous_ofAdd.comp
        ((continuous_residueRingHom n (NeZero.ne n)).comp continuous_toAdd)⟩
  exact f.comp (primewisePadicRingMultiplicativeEquiv.symm : _ →ₜ* _)

private theorem residueContinuousMulHom_apply (n : ℕ) [NeZero n]
    (x : primewisePadicRing.{u}) :
    residueContinuousMulHom n
        (primewisePadicRingMultiplicativeEquiv (Multiplicative.ofAdd x)) =
      Multiplicative.ofAdd (residueRingHom n (NeZero.ne n) x) := by
  rfl

private theorem residueContinuousMulHom_generator (n : ℕ) [NeZero n] :
    residueContinuousMulHom.{u} n primewisePadicGenerator =
      finiteCyclicGenerator n := by
  have hgen : primewisePadicRingMultiplicativeEquiv.{u}
      (Multiplicative.ofAdd (1 : primewisePadicRing.{u})) =
        primewisePadicGenerator := by
    funext p
    rfl
  rw [← hgen, residueContinuousMulHom_apply]
  exact congrArg Multiplicative.ofAdd
    (map_one (residueRingHom.{u} n (NeZero.ne n)))

/-- The primewise exponents of a finite cyclic profinite group of positive
order are exactly the prime multiplicities of its order. -/
theorem finiteCyclic_exponents_eq_factorization (n : ℕ) [NeZero n]
    (p : Nat.Primes) :
    (finiteCyclic_isProcyclic n).exponents p = (n.factorization p.1 : ℕ∞) := by
  let hn : n ≠ 0 := NeZero.ne n
  have hmaps : residueContinuousMulHom.{0} n =
      primewisePadicBaseMapOfGenerator (finiteCyclic n) (finiteCyclicGenerator n) := by
    apply ContinuousMonoidHom.ext
    intro x
    have heq := (denseRange_primewisePadicDiagonal.{0}).equalizer
      (residueContinuousMulHom.{0} n).continuous_toFun
      (primewisePadicBaseMapOfGenerator (finiteCyclic n)
        (finiteCyclicGenerator n)).continuous_toFun (by
        funext k
        have hpower : primewisePadicGenerator.{0} ^ k =
            primewisePadicDiagonal k := by
          funext q
          exact primewisePadicGenerator_zpow k q
        calc
          residueContinuousMulHom n (primewisePadicDiagonal k) =
              residueContinuousMulHom n (primewisePadicGenerator ^ k) :=
                congrArg _ hpower.symm
          _ = finiteCyclicGenerator n ^ k := by
            rw [map_zpow, residueContinuousMulHom_generator]
          _ = primewisePadicBaseMapOfGenerator (finiteCyclic n)
              (finiteCyclicGenerator n) (primewisePadicDiagonal k) :=
                (primewisePadicBaseMapOfGenerator_diagonal _ _ k).symm)
    exact congrFun heq x
  have hker : primewisePadicKernelIdeal
      (primewisePadicBaseMapOfGenerator (finiteCyclic n) (finiteCyclicGenerator n)) =
      RingHom.ker (residueRingHom.{0} n hn) := by
    ext x
    rw [mem_primewisePadicKernelIdeal, RingHom.mem_ker, ← hmaps,
      residueContinuousMulHom_apply]
    change Multiplicative.ofAdd (residueRingHom n hn x) =
      Multiplicative.ofAdd (0 : ZMod n) ↔ residueRingHom n hn x = 0
    exact Multiplicative.ofAdd.injective.eq_iff
  rw [(finiteCyclic_isProcyclic n).exponents_eq_baseMap_of_generator
    (finiteCyclicGenerator n) (finiteCyclicGenerator_isTopologicalGenerator n)]
  change primewisePadicIdealExponents
    (primewisePadicKernelIdeal
      (primewisePadicBaseMapOfGenerator (finiteCyclic n) (finiteCyclicGenerator n))) p = _
  rw [hker, residueRingHom_ker, primewisePadicIdealExponents_idealOfExponents]

/-- If the index of the `n`-th power image is `n`, a supplied topological
generator determines the continuous equivalence from the multiplicative
`ZMod n` to the finite quotient, sending the additive class of one to its
quotient class. The inverse gives the corresponding map to `ZMod n`. -/
noncomputable def powerImage_zmodContinuousMulEquiv (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (n : ℕ) (hn : 0 < n)
    (hindex : (powerImage G hG n : Subgroup G).index = n) :
    Multiplicative (ZMod n) ≃ₜ*
      (G ⧸ (powerImage G hG n : Subgroup G)) := by
  let H := (powerImage G hG n : Subgroup G)
  letI : DiscreteTopology (G ⧸ H) :=
    QuotientGroup.discreteTopology (powerImage_isOpen G hG n hn)
  have hgen : ∀ x : G ⧸ H,
      x ∈ Subgroup.zpowers ((QuotientGroup.mk' H) g) := by
    intro x
    rw [powerImage_quotient_zpowers_eq_top G hG g hg n hn]
    trivial
  have hcard : Nat.card (G ⧸ H) = n := H.index_eq_card.symm.trans hindex
  exact ContinuousMulEquiv.mk
    (zmodMulEquivOfGenerator hgen hcard)
    continuous_of_discreteTopology continuous_of_discreteTopology

/-- The chosen equivalence maps additive one to the quotient class of the
supplied topological generator. -/
@[simp] theorem powerImage_zmodContinuousMulEquiv_apply_one
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (g : G) (hg : IsTopologicalGenerator G g) (n : ℕ) (hn : 0 < n)
    (hindex : (powerImage G hG n : Subgroup G).index = n) :
    powerImage_zmodContinuousMulEquiv G hG g hg n hn hindex
      (Multiplicative.ofAdd (1 : ZMod n)) =
        (QuotientGroup.mk' (powerImage G hG n : Subgroup G)) g := by
  have hgen : ∀ x : G ⧸ (powerImage G hG n : Subgroup G),
      x ∈ Subgroup.zpowers
        ((QuotientGroup.mk' (powerImage G hG n : Subgroup G)) g) := by
    intro x
    rw [powerImage_quotient_zpowers_eq_top G hG g hg n hn]
    trivial
  have hcard : Nat.card (G ⧸ (powerImage G hG n : Subgroup G)) = n :=
    (powerImage G hG n : Subgroup G).index_eq_card.symm.trans hindex
  change zmodMulEquivOfGenerator hgen hcard (Multiplicative.ofAdd 1) = _
  exact zmodMulEquivOfGenerator_apply_ofAdd_one hgen hcard

/-- The inverse of the chosen equivalence sends the quotient class of the
supplied topological generator to additive one. -/
@[simp] theorem powerImage_zmodContinuousMulEquiv_symm_apply_generator
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (g : G) (hg : IsTopologicalGenerator G g) (n : ℕ) (hn : 0 < n)
    (hindex : (powerImage G hG n : Subgroup G).index = n) :
    (powerImage_zmodContinuousMulEquiv G hG g hg n hn hindex).symm
      ((QuotientGroup.mk' (powerImage G hG n : Subgroup G)) g) =
        Multiplicative.ofAdd (1 : ZMod n) := by
  rw [← powerImage_zmodContinuousMulEquiv_apply_one G hG g hg n hn hindex]
  exact (powerImage_zmodContinuousMulEquiv G hG g hg n hn hindex).symm_apply_apply _

/-- A positive power image has index exactly `n` if and only if every prime
multiplicity of `n` fits in the corresponding (possibly infinite) procyclic
exponent. For positive `n`, `n.factorization p` is `Nat.multiplicity p n`.

The supported indices in Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7
motivate this more general exact-index criterion, using Mathlib’s factorization and `ZMod`
API. -/
theorem powerImage_index_eq_iff_exponents (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (n : ℕ) (hn : 0 < n) :
    (powerImage G hG n : Subgroup G).index = n ↔
      ∀ p : Nat.Primes, (n.factorization p.1 : ℕ∞) ≤ hG.exponents p := by
  let _ : NeZero n := ⟨hn.ne'⟩
  let hH := finiteCyclic_isProcyclic n
  have hcard : Nat.card (finiteCyclic n) = n := by
    change Nat.card (Multiplicative (ZMod n)) = n
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  constructor
  · intro hindex
    let g := hG.choose
    have hg : IsTopologicalGenerator G g := hG.choose_spec
    let e := powerImage_zmodContinuousMulEquiv G hG g hg n hn hindex
    let f : G →ₜ* finiteCyclic n :=
      ⟨e.symm.toMonoidHom.comp (QuotientGroup.mk' (powerImage G hG n : Subgroup G)),
        e.symm.continuous_toFun.comp QuotientGroup.continuous_mk⟩
    have hf : Function.Surjective f :=
      e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
    have hbound := (exists_surjective_continuousHom_iff_exponents_le hG hH).mp ⟨f, hf⟩
    intro p
    rw [← finiteCyclic_exponents_eq_factorization n p]
    exact hbound p
  · intro hbound
    obtain ⟨f, hf⟩ := (exists_surjective_continuousHom_iff_exponents_le hG hH).mpr
      (fun p ↦ by rw [finiteCyclic_exponents_eq_factorization]; exact hbound p)
    have hker : (powerImage G hG n : Subgroup G) ≤ f.toMonoidHom.ker := by
      intro x hx
      obtain ⟨y, rfl⟩ := (mem_powerImage_iff G hG n x).mp hx
      change f (y ^ n) = 1
      rw [map_pow]
      exact (congrArg (fun exponent : ℕ ↦ f y ^ exponent) hcard).symm.trans
        (pow_card_eq_one' (x := f y))
    have hsurj : f.toMonoidHom.ker.index = n := by
      rw [Subgroup.index_ker]
      have hrange : Function.Surjective
          ((↑) : f.toMonoidHom.range → finiteCyclic n) := by
        intro y
        exact ⟨⟨y, hf y⟩, rfl⟩
      calc
        Nat.card f.toMonoidHom.range = Nat.card (finiteCyclic n) :=
          Nat.card_congr (Equiv.ofBijective Subtype.val
            ⟨Subtype.coe_injective, hrange⟩)
        _ = n := hcard
    have hindex_dvd : n ∣ (powerImage G hG n : Subgroup G).index := by
      calc
        n = f.toMonoidHom.ker.index := hsurj.symm
        _ ∣ _ := Subgroup.index_dvd_of_le hker
    exact Nat.dvd_antisymm (powerImage_index_dvd G hG n hn) hindex_dvd

/-- For a torsion-free procyclic group, a positive power image has exact
index if and only if every prime dividing `n` has infinite exponent.

This is the torsion-free supported-index specialization of the description in
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
(1.7.7). -/
theorem powerImage_index_eq_iff_exponents_top_of_isMulTorsionFree
    (G : ProfiniteGrp.{u}) (hG : IsProcyclic G)
    (hfree : IsMulTorsionFree G) (n : ℕ) (hn : 0 < n) :
    (powerImage G hG n : Subgroup G).index = n ↔
      ∀ p : Nat.Primes, n.factorization p.1 ≠ 0 → hG.exponents p = ⊤ := by
  let g := hG.choose
  have hg : IsTopologicalGenerator G g := hG.choose_spec
  have hexponents : ∀ p : Nat.Primes, hG.exponents p = 0 ∨
      hG.exponents p = ⊤ := by
    simpa only [hG.exponents_eq_of_generator g hg] using
      (isMulTorsionFree_iff_exponentsOfGenerator G g hg).mp hfree
  rw [powerImage_index_eq_iff_exponents G hG n hn]
  constructor
  · intro h p hp
    rcases hexponents p with hzero | htop
    · have hbound := h p
      rw [hzero] at hbound
      have : n.factorization p.1 = 0 :=
        Nat.eq_zero_of_le_zero (ENat.natCast_le_natCast.mp hbound)
      exact (hp this).elim
    · exact htop
  · intro h p
    by_cases hp : n.factorization p.1 = 0
    · simp [hp]
    · simp [h p hp]

end ProfiniteGrp
