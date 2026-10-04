/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.Procyclic
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Data.ZMod.QuotientRing

/-!
# The primewise p-adic profinite group

This file constructs the product of the additive groups of the p-adic integers,
written multiplicatively, and proves that its integral diagonal is dense.  It
also proves that the resulting canonical map from the profinite completion of
the integers is an equivalence of topological groups.

The construction is universe-polymorphic: every p-adic factor is universe
lifted before forming the product.  In particular, no countability,
metrizability, nontriviality, or same-universe hypothesis is imposed on clients.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (primewise p-adic model of the completed integers).
- Mathlib, `Mathlib.NumberTheory.Padics.RingHoms`, `Mathlib.Data.Nat.ChineseRemainder` and
  `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion` (p-adic factors and
  completion).
-/

@[expose] public section

open CategoryTheory Function Set
open CategoryTheory.Limits

universe u

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The additive group of `p`-adic integers, written multiplicatively as a
profinite group in an arbitrary universe. -/
noncomputable def padicFactor (p : Nat.Primes) : ProfiniteGrp.{u} := by
  letI : CompactSpace (ULift.{u} ℤ_[p.1]) :=
    Homeomorph.compactSpace (Homeomorph.ulift (X := ℤ_[p.1])).symm
  letI : TotallyDisconnectedSpace (ULift.{u} ℤ_[p.1]) :=
    Homeomorph.totallyDisconnectedSpace (Homeomorph.ulift (X := ℤ_[p.1])).symm
  exact ProfiniteGrp.of (Multiplicative (ULift.{u} ℤ_[p.1]))

/-- The product of the additive groups of the `p`-adic integers over all
primes, written multiplicatively. -/
noncomputable def primewisePadic : ProfiniteGrp.{u} :=
  ProfiniteGrp.pi padicFactor

/-- The integral diagonal in the primewise p-adic product. -/
noncomputable def primewisePadicDiagonal (n : ℤ) : primewisePadic.{u} := by
  change ∀ p : Nat.Primes, padicFactor p
  intro p
  change Multiplicative (ULift.{u} ℤ_[p.1])
  exact Multiplicative.ofAdd (ULift.up (n : ℤ_[p.1]))

/-- The coordinates of the integral diagonal are the corresponding casts into
the p-adic integers. -/
@[simp]
theorem primewisePadicDiagonal_apply (n : ℤ) (p : Nat.Primes) :
    primewisePadicDiagonal.{u} n p =
      Multiplicative.ofAdd (ULift.up (n : ℤ_[p.1])) := by
  rfl

/-- The primewise element whose coordinate at every prime is `1`. -/
noncomputable def primewisePadicGenerator : primewisePadic.{u} :=
  primewisePadicDiagonal 1

/-- Integral powers of the canonical generator are the integral diagonal. -/
@[simp]
theorem primewisePadicGenerator_zpow (n : ℤ) (p : Nat.Primes) :
    (primewisePadicGenerator.{u} ^ n) p =
      Multiplicative.ofAdd (ULift.up (n : ℤ_[p.1])) := by
  change (Multiplicative.ofAdd (ULift.up (1 : ℤ_[p.1])) ^ n) = _
  apply Multiplicative.toAdd.injective
  change n • (ULift.up (1 : ℤ_[p.1])) = ULift.up (n : ℤ_[p.1])
  apply ULift.down_injective
  simp

/-- The integral diagonal is dense in the product of all p-adic additive
groups.  Only finitely many coordinates occur in a basic product-open set, and
the Chinese remainder theorem simultaneously meets their p-power
congruences. -/
theorem denseRange_primewisePadicDiagonal :
    DenseRange (primewisePadicDiagonal.{u}) := by
  change DenseRange (fun n : ℤ ↦ fun p : Nat.Primes ↦
    Multiplicative.ofAdd (ULift.up (n : ℤ_[p.1])))
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨x, hx⟩
  rcases (isOpen_pi_iff.mp hU) x hx with ⟨J, V, hV, hVU⟩
  let w : (p : J) → Set ℤ_[p.1.1] := fun p ↦
    (fun z : ℤ_[p.1.1] ↦ Multiplicative.ofAdd (ULift.up z)) ⁻¹' V p.1
  have hwOpen (p : J) : IsOpen (w p) := by
    apply (hV p.1 p.2).1.preimage
    fun_prop
  have hwNonempty (p : J) : (w p).Nonempty := by
    refine ⟨(x p.1).toAdd.down, ?_⟩
    exact (hV p.1 p.2).2
  have hApprox (p : J) : ∃ a : ℕ, (a : ℤ_[p.1.1]) ∈ w p := by
    exact (PadicInt.denseRange_natCast (p := p.1.1)).exists_mem_open
      (hwOpen p) (hwNonempty p)
  choose a ha using hApprox
  have hRadius (p : J) : ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (a p : ℤ_[p.1.1]) ε ⊆ w p := by
    exact (Metric.isOpen_iff.mp (hwOpen p)) _ (ha p)
  choose ε hε hball using hRadius
  have hPower (p : J) : ∃ k : ℕ,
      (p.1.1 : ℝ) ^ (-(k : ℤ)) < ε p := by
    exact PadicInt.exists_pow_neg_lt p.1.1 (hε p)
  choose k hk using hPower
  have hmodNe : ∀ p : J, p.1.1 ^ k p ≠ 0 := by
    intro p
    exact pow_ne_zero _ p.1.2.ne_zero
  have hpair : Set.Pairwise (Set.univ : Set J)
      (Nat.Coprime on fun p : J ↦ p.1.1 ^ k p) := by
    intro p _ q _ hpq
    apply Nat.coprime_pow_primes (k p) (k q) p.1.2 q.1.2
    intro hpqVal
    apply hpq
    apply Subtype.ext
    apply Subtype.ext
    exact hpqVal
  let z := Nat.chineseRemainderOfFinset a (fun p : J ↦ p.1.1 ^ k p)
    Finset.univ (by simpa using hmodNe) (by simpa using hpair)
  let n : ℤ := z.1
  refine ⟨fun p : Nat.Primes ↦
      Multiplicative.ofAdd (ULift.up (n : ℤ_[p.1])), ?_, ⟨n, rfl⟩⟩
  apply hVU
  intro p hp
  let jp : J := ⟨p, hp⟩
  have hzMod : z.1 ≡ a jp [MOD p.1 ^ k jp] := z.2 jp (by simp)
  have hzDvd : (p.1 ^ k jp : ℤ) ∣ n - (a jp : ℤ) := by
    have h := hzMod.dvd
    simpa [n] using dvd_neg.mpr h
  apply hball jp
  rw [Metric.mem_ball, dist_eq_norm]
  apply lt_of_le_of_lt _ (hk jp)
  simpa only [Int.cast_sub, Int.cast_natCast] using
    (PadicInt.norm_int_le_pow_iff_dvd (p := p.1) (k := n - (a jp : ℤ))
      (n := k jp)).mpr hzDvd

/-- The canonical element topologically generates the primewise p-adic
product. -/
theorem primewisePadicGenerator_isTopologicalGenerator :
    IsTopologicalGenerator primewisePadic.{u} primewisePadicGenerator := by
  rw [IsTopologicalGenerator]
  rw [show (fun n : ℤ ↦ primewisePadicGenerator.{u} ^ n) =
      primewisePadicDiagonal.{u} by
    funext n
    funext p
    exact primewisePadicGenerator_zpow n p]
  exact denseRange_primewisePadicDiagonal

/-- The primewise p-adic product is procyclic. -/
theorem primewisePadic_isProcyclic : IsProcyclic primewisePadic.{u} :=
  ⟨primewisePadicGenerator, primewisePadicGenerator_isTopologicalGenerator⟩

/-- The canonical map from the profinite completion of the integers to the
primewise p-adic product. -/
noncomputable def integerCompletionToPrimewisePadic :
    integerCompletion.{u} ⟶ primewisePadic.{u} :=
  integerCompletionMap primewisePadic primewisePadicGenerator

/-- The canonical completion map restricts to the integral diagonal. -/
@[simp]
theorem integerCompletionToPrimewisePadic_eta_int (n : ℤ) :
    integerCompletionToPrimewisePadic.{u}
        (ProfiniteCompletion.etaFn
          (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
          (ULift.up (Multiplicative.ofAdd n))) =
      primewisePadicDiagonal n := by
  rw [integerCompletionToPrimewisePadic, integerCompletionMap_eta_int]
  funext p
  exact primewisePadicGenerator_zpow n p

/-- The canonical map from the profinite completion onto the primewise p-adic
product is surjective. -/
theorem integerCompletionToPrimewisePadic_surjective :
    Function.Surjective integerCompletionToPrimewisePadic.{u} := by
  exact (isTopologicalGenerator_iff_surjective_integerCompletionMap
    primewisePadic primewisePadicGenerator).mp
      primewisePadicGenerator_isTopologicalGenerator

/-- The continuous additive residue map from the completed integers at a
positive modulus, written multiplicatively. -/
noncomputable def integerCompletionResidueHom (n : ℕ) [NeZero n] :
    integerCompletion.{u} ⟶
      ProfiniteGrp.ofFiniteGrp
        (FiniteGrp.of (Multiplicative (ULift.{u} (ZMod n)))) :=
  integerCompletionMap _ (Multiplicative.ofAdd (ULift.up (1 : ZMod n)))

/-- Evaluation of the completed integers in the finite additive residue group. -/
noncomputable def integerCompletionResidue (n : ℕ) [NeZero n]
    (x : integerCompletion.{u}) : Multiplicative (ULift.{u} (ZMod n)) :=
  integerCompletionResidueHom.{u} n x

/-- The completed-integer residue map is continuous at every positive modulus. -/
theorem continuous_integerCompletionResidue (n : ℕ) [NeZero n] :
    Continuous (integerCompletionResidue.{u} n) := by
  let P := ProfiniteGrp.ofFiniteGrp
    (FiniteGrp.of (Multiplicative (ULift.{u} (ZMod n))))
  have htop : (inferInstance : TopologicalSpace
      (Multiplicative (ULift.{u} (ZMod n)))) =
      P.toProfinite.toTop.str := by
    rw [DiscreteTopology.eq_bot (α := Multiplicative (ULift.{u} (ZMod n)))]
    rfl
  change @Continuous _ _ _ (inferInstance : TopologicalSpace
    (Multiplicative (ULift.{u} (ZMod n)))) _
  rw [htop]
  exact (integerCompletionResidueHom.{u} n).hom.continuous_toFun

/-- Integral casts reduce to the usual residue at a positive modulus. -/
@[simp] theorem integerCompletionResidue_eta (n : ℕ) [NeZero n]
    (z : ULift.{u} (Multiplicative ℤ)) :
    integerCompletionResidue.{u} n (ProfiniteCompletion.etaFn _ z) =
      Multiplicative.ofAdd (ULift.up (z.down.toAdd : ZMod n)) := by
  change integerCompletionMap
      (ProfiniteGrp.ofFiniteGrp
        (FiniteGrp.of (Multiplicative (ULift.{u} (ZMod n)))))
      (Multiplicative.ofAdd (ULift.up (1 : ZMod n)))
      (ProfiniteCompletion.etaFn _ z) = _
  calc
    _ = (Multiplicative.ofAdd (ULift.up (1 : ZMod n))) ^ z.down.toAdd :=
      integerCompletionMap_eta _ _ z
    _ = _ := by
      apply Multiplicative.toAdd.injective
      apply ULift.down_injective
      simp

/-- Reduction of p-adic integers modulo a prime power is continuous. -/
theorem continuous_toZModPow (p : Nat.Primes) (k : ℕ) :
    Continuous (@PadicInt.toZModPow p.1 (inferInstance : Fact p.1.Prime) k) := by
  apply continuous_of_continuousAt_zero (PadicInt.toZModPow k).toAddMonoidHom
  rw [ContinuousAt]
  rw [show nhds ((PadicInt.toZModPow k).toAddMonoidHom 0) =
      pure ((PadicInt.toZModPow k).toAddMonoidHom 0) by
    exact congrFun (nhds_discrete (ZMod (p.1 ^ k))) _]
  rw [map_zero, Filter.tendsto_pure]
  change (((@PadicInt.toZModPow p.1
    (inferInstance : Fact p.1.Prime) k).toAddMonoidHom).ker :
      Set ℤ_[p.1]) ∈ nhds 0
  apply IsOpen.mem_nhds
  · change IsOpen (RingHom.ker (@PadicInt.toZModPow p.1
      (inferInstance : Fact p.1.Prime) k) : Set ℤ_[p.1])
    rw [PadicInt.ker_toZModPow]
    have hr : (p.1 : ℝ) ^ (-(k : ℤ)) ≠ 0 :=
      zpow_ne_zero _ (mod_cast p.2.ne_zero)
    have heq :
        ((Ideal.span {(p.1 : ℤ_[p.1]) ^ k} : Ideal ℤ_[p.1]) : Set ℤ_[p.1]) =
          Metric.closedBall 0 ((p.1 : ℝ) ^ (-(k : ℤ))) := by
      ext z
      change z ∈ (Ideal.span {(p.1 : ℤ_[p.1]) ^ k} : Ideal ℤ_[p.1]) ↔
        dist z 0 ≤ (p.1 : ℝ) ^ (-(k : ℤ))
      rw [dist_zero_right]
      exact (PadicInt.norm_le_pow_iff_mem_span_pow z k).symm
    rw [heq]
    exact IsUltrametricDist.isOpen_closedBall 0 hr
  · exact (@PadicInt.toZModPow p.1
      (inferInstance : Fact p.1.Prime) k).map_zero

private theorem residue_eq_padic_reduction (p : Nat.Primes) (k : ℕ)
    (x : integerCompletion.{u}) :
    (integerCompletionResidue.{u} (p.1 ^ k) x).toAdd.down =
      PadicInt.toZModPow k
        ((integerCompletionToPrimewisePadic x p).toAdd.down) := by
  let f : integerCompletion.{u} → ZMod (p.1 ^ k) := fun y ↦
    (integerCompletionResidue.{u} (p.1 ^ k) y).toAdd.down
  let g : integerCompletion.{u} → ZMod (p.1 ^ k) := fun y ↦
    PadicInt.toZModPow k ((integerCompletionToPrimewisePadic y p).toAdd.down)
  suffices f = g by exact congrFun this x
  refine (ProfiniteCompletion.denseRange
      (G := GrpCat.of (ULift.{u} (Multiplicative ℤ)))).equalizer ?_ ?_ ?_
  · exact (continuous_uliftDown.comp continuous_toAdd).comp
      (continuous_integerCompletionResidue.{u} (p.1 ^ k))
  · exact (continuous_toZModPow p k).comp
      (continuous_uliftDown.comp (continuous_toAdd.comp
        ((continuous_apply p).comp
          integerCompletionToPrimewisePadic.hom.continuous_toFun)))
  · funext z
    dsimp only [Function.comp_apply, f, g]
    rw [integerCompletionResidue_eta]
    rw [show integerCompletionToPrimewisePadic.{u}
        (ProfiniteCompletion.etaFn _ z) p =
      Multiplicative.ofAdd (ULift.up (z.down.toAdd : ℤ_[p.1])) by
      rw [integerCompletionToPrimewisePadic, integerCompletionMap_eta]
      apply Multiplicative.toAdd.injective
      apply ULift.down_injective
      change z.down.toAdd • (1 : ℤ_[p.1]) = (z.down.toAdd : ℤ_[p.1])
      simp]
    change (z.down.toAdd : ZMod (p.1 ^ k)) =
      PadicInt.toZModPow k (z.down.toAdd : ℤ_[p.1])
    exact (map_intCast (PadicInt.toZModPow k) z.down.toAdd).symm

private noncomputable def residueToQuotient
    (H : FiniteIndexNormalSubgroup (ULift.{u} (Multiplicative ℤ))) :
    Multiplicative (ULift.{u} (ZMod
      (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)))) →*
      (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup) := by
  let Q := ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup
  let q : Q := QuotientGroup.mk (ULift.up (Multiplicative.ofAdd (1 : ℤ)))
  let f : ℤ →+ Additive Q := zmultiplesHom (Additive Q) (Additive.ofMul q)
  have hf : f (Nat.card Q) = 0 := by
    change Additive.ofMul (q ^ (Nat.card Q : ℤ)) = 0
    rw [zpow_natCast, pow_card_eq_one']
    rfl
  let fmod : ZMod (Nat.card Q) →+ Additive Q := ZMod.lift _ ⟨f, hf⟩
  exact {
    toFun := fun z ↦ (fmod z.toAdd.down).toMul
    map_one' := by simp [fmod]
    map_mul' := by
      intro x y
      change (fmod (x.toAdd.down + y.toAdd.down)).toMul = _
      rw [fmod.map_add]
      rfl }

private theorem residueToQuotient_cast
    (H : FiniteIndexNormalSubgroup (ULift.{u} (Multiplicative ℤ))) (m : ℤ) :
    residueToQuotient H
        (Multiplicative.ofAdd (ULift.up
          (m : ZMod (Nat.card
            (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup))))) =
      QuotientGroup.mk (ULift.up (Multiplicative.ofAdd m)) := by
  simp only [residueToQuotient, ULift.up_intCast, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, ULift.down_intCast, ZMod.lift_coe, zmultiplesHom_apply, toMul_zsmul,
    toMul_ofMul]
  rw [← QuotientGroup.mk_zpow]
  congr 1
  apply ULift.down_injective
  apply Multiplicative.toAdd.injective
  simp

private noncomputable def integerCompletionProjection
    (H : FiniteIndexNormalSubgroup (ULift.{u} (Multiplicative ℤ))) :
    integerCompletion.{u} ⟶
      (ProfiniteCompletion.diagram
        (GrpCat.of (ULift.{u} (Multiplicative ℤ)))).obj H := by
  unfold integerCompletion ProfiniteCompletion.completion
  exact (ProfiniteGrp.limitCone (ProfiniteCompletion.diagram
    (GrpCat.of (ULift.{u} (Multiplicative ℤ))))).π.app H

private noncomputable def residueToQuotientHom
    (H : FiniteIndexNormalSubgroup (ULift.{u} (Multiplicative ℤ))) :
    ProfiniteGrp.ofFiniteGrp
        (FiniteGrp.of (Multiplicative (ULift.{u} (ZMod
          (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)))))) ⟶
      (ProfiniteCompletion.diagram
        (GrpCat.of (ULift.{u} (Multiplicative ℤ)))).obj H := by
  apply ConcreteCategory.ofHom
  exact { residueToQuotient H with
    continuous_toFun := by
      change @Continuous _ _ ⊥ _ _
      exact continuous_bot }

private theorem integerCompletionProjection_eq_residue
    (H : FiniteIndexNormalSubgroup (ULift.{u} (Multiplicative ℤ))) :
    integerCompletionProjection H =
      integerCompletionResidueHom.{u}
          (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)) ≫
        residueToQuotientHom H := by
  let _ : NeZero (Nat.card
      (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)) :=
    ⟨Nat.card_pos.ne'⟩
  ext x
  apply congrFun
  refine (ProfiniteCompletion.denseRange
    (G := GrpCat.of (ULift.{u} (Multiplicative ℤ)))).equalizer
      (integerCompletionProjection H).hom.continuous_toFun
      (integerCompletionResidueHom.{u}
          (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)) ≫
        residueToQuotientHom H).hom.continuous_toFun ?_
  funext z
  dsimp only [Function.comp_apply]
  rw [ProfiniteGrp.comp_apply]
  change QuotientGroup.mk z = residueToQuotient H
    (integerCompletionResidueHom.{u}
      (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup))
      (ProfiniteCompletion.etaFn _ z))
  have heta : integerCompletionResidueHom.{u}
      (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup))
      (ProfiniteCompletion.etaFn _ z) =
      (Multiplicative.ofAdd (ULift.up (1 : ZMod
        (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup))))) ^
        z.down.toAdd := by
    exact integerCompletionMap_eta _ _ z
  rw [heta]
  change QuotientGroup.mk z = residueToQuotient H
    ((Multiplicative.ofAdd (ULift.up (1 : ZMod
      (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup))))) ^ z.down.toAdd)
  rw [show (Multiplicative.ofAdd (ULift.up (1 : ZMod
      (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup))))) ^ z.down.toAdd =
      Multiplicative.ofAdd (ULift.up (z.down.toAdd : ZMod
        (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)))) by
    apply Multiplicative.toAdd.injective
    apply ULift.down_injective
    simp]
  rw [residueToQuotient_cast]
  congr 1

/-- The residues at all positive moduli determine an element of the completed integers. -/
theorem integerCompletionResidue_jointly_injective
    {x y : integerCompletion.{u}}
    (h : ∀ (n : ℕ) [NeZero n],
      integerCompletionResidue.{u} n x = integerCompletionResidue.{u} n y) :
    x = y := by
  unfold integerCompletion ProfiniteCompletion.completion at x y
  apply Subtype.ext
  funext H
  let _ : NeZero (Nat.card
      (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)) :=
    ⟨Nat.card_pos.ne'⟩
  have hcoord := ConcreteCategory.congr_hom
    (integerCompletionProjection_eq_residue H)
  have hxcoord := hcoord x
  change x.1 H = residueToQuotient H
    (integerCompletionResidue.{u}
      (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)) x) at hxcoord
  have hycoord := hcoord y
  change y.1 H = residueToQuotient H
    (integerCompletionResidue.{u}
      (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)) y) at hycoord
  have hres := h (Nat.card
    (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup))
  have hmap : residueToQuotient H
      (integerCompletionResidue.{u}
        (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)) x) =
      residueToQuotient H
      (integerCompletionResidue.{u}
        (Nat.card (ULift.{u} (Multiplicative ℤ) ⧸ H.toSubgroup)) y) :=
    congrArg (fun z ↦ residueToQuotient H z) hres
  exact hxcoord.trans (hmap.trans hycoord.symm)

/-- Completed-integer residues commute with reduction between positive moduli. -/
theorem integerCompletionResidue_cast {d n : ℕ} [NeZero d] [NeZero n]
    (hd : d ∣ n) (x : integerCompletion.{u}) :
    ZMod.cast (integerCompletionResidue.{u} n x).toAdd.down =
      (integerCompletionResidue.{u} d x).toAdd.down := by
  let f : integerCompletion.{u} → ZMod d := fun y ↦
    ZMod.cast (integerCompletionResidue.{u} n y).toAdd.down
  let g : integerCompletion.{u} → ZMod d := fun y ↦
    (integerCompletionResidue.{u} d y).toAdd.down
  suffices f = g by exact congrFun this x
  refine (ProfiniteCompletion.denseRange
      (G := GrpCat.of (ULift.{u} (Multiplicative ℤ)))).equalizer ?_ ?_ ?_
  · exact continuous_of_discreteTopology.comp <|
      (continuous_uliftDown.comp continuous_toAdd).comp
        (continuous_integerCompletionResidue.{u} n)
  · exact (continuous_uliftDown.comp continuous_toAdd).comp
      (continuous_integerCompletionResidue.{u} d)
  · funext z
    dsimp only [Function.comp_apply, f, g]
    rw [integerCompletionResidue_eta, integerCompletionResidue_eta]
    exact ZMod.cast_intCast hd z.down.toAdd

private theorem zmod_equivPi_apply (n : ℕ) (hn : n ≠ 0) (z : ZMod n)
    (p : n.primeFactors) :
    ZMod.equivPi n hn z p = ZMod.cast (z : ZMod n) := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective z
  have hd : p.1 ^ n.factorization p.1 ∣ n :=
    ((Nat.prime_of_mem_primeFactors p.2).pow_dvd_iff_le_factorization hn).2 le_rfl
  rw [ZMod.equivPi, RingEquiv.trans_apply, ZMod.prodEquivPi_apply,
    ZMod.ringEquivCongr_intCast]
  calc
    _ = (m : ZMod (p.1 ^ n.factorization p.1)) := map_intCast _ m
    _ = ZMod.cast (m : ZMod n) := (ZMod.cast_intCast hd m).symm

private theorem integerCompletionResidue_eq_of_primewise_eq
    {x y : integerCompletion.{u}}
    (hxy : integerCompletionToPrimewisePadic.{u} x =
      integerCompletionToPrimewisePadic.{u} y)
    (n : ℕ) [NeZero n] :
    integerCompletionResidue.{u} n x = integerCompletionResidue.{u} n y := by
  apply Multiplicative.toAdd.injective
  apply ULift.down_injective
  apply (ZMod.equivPi n (NeZero.ne n)).injective
  funext q
  rw [zmod_equivPi_apply, zmod_equivPi_apply]
  let p : Nat.Primes := ⟨q.1, Nat.prime_of_mem_primeFactors q.2⟩
  let k := n.factorization p.1
  let _ : NeZero (p.1 ^ k) := ⟨pow_ne_zero _ p.2.ne_zero⟩
  have hd : p.1 ^ k ∣ n :=
    (p.2.pow_dvd_iff_le_factorization (NeZero.ne n)).2 le_rfl
  rw [integerCompletionResidue_cast hd x,
    integerCompletionResidue_cast hd y]
  rw [residue_eq_padic_reduction p k,
    residue_eq_padic_reduction p k]
  exact congrArg
    (fun z : primewisePadic.{u} ↦
      PadicInt.toZModPow k ((z p).toAdd.down)) hxy

/-- The canonical map from the profinite completion of the integers to the
primewise p-adic product is injective. -/
theorem integerCompletionToPrimewisePadic_injective :
    Function.Injective integerCompletionToPrimewisePadic.{u} := by
  intro x y hxy
  apply integerCompletionResidue_jointly_injective
  intro n _
  exact integerCompletionResidue_eq_of_primewise_eq hxy n

/-- The canonical continuous multiplicative equivalence from the profinite
completion of the integers to the product of the additive p-adic integers.

This formalizes the primewise p-adic product in Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Ch. I §7, before Proposition (1.7.7). -/
noncomputable def integerCompletionEquivPrimewisePadic :
    integerCompletion.{u} ≃ₜ* primewisePadic.{u} :=
  ContinuousMulEquiv.mk'
    ((isHomeomorph_iff_continuous_bijective.mpr
      ⟨integerCompletionToPrimewisePadic.hom.continuous_toFun,
        integerCompletionToPrimewisePadic_injective,
        integerCompletionToPrimewisePadic_surjective⟩).homeomorph
      (fun x ↦ integerCompletionToPrimewisePadic x))
    integerCompletionToPrimewisePadic.hom.map_mul

/-- The canonical equivalence has the canonical completion morphism as its
underlying map. -/
@[simp]
theorem integerCompletionEquivPrimewisePadic_apply
    (x : integerCompletion.{u}) :
    integerCompletionEquivPrimewisePadic.{u} x =
      integerCompletionToPrimewisePadic x := by
  rfl

/-- The canonical equivalence restricts to the integral diagonal. -/
theorem integerCompletionEquivPrimewisePadic_eta_int (n : ℤ) :
    integerCompletionEquivPrimewisePadic.{u}
        (ProfiniteCompletion.etaFn
          (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
          (ULift.up (Multiplicative.ofAdd n))) =
      primewisePadicDiagonal n := by
  rw [integerCompletionEquivPrimewisePadic_apply,
    integerCompletionToPrimewisePadic_eta_int]

/-- The inverse of the canonical equivalence takes the integral diagonal to
the corresponding element of the profinite completion. -/
@[simp]
theorem integerCompletionEquivPrimewisePadic_symm_diagonal (n : ℤ) :
    integerCompletionEquivPrimewisePadic.{u}.symm
        (primewisePadicDiagonal n) =
      ProfiniteCompletion.etaFn
        (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
        (ULift.up (Multiplicative.ofAdd n)) := by
  apply integerCompletionEquivPrimewisePadic.injective
  simp

end ProfiniteGrp
