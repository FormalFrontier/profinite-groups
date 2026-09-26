/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.EpiMono
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Instances.ZMod

/-!
# Procyclic profinite groups

This file defines topological generators and procyclicity for profinite groups,
constructs the canonical map from the profinite completion of the integers, and
gives transport results and finite cyclic examples.  Additive-native generator,
transport, and example APIs are provided in `ProfiniteAddGrp`.
-/

@[expose] public section

open CategoryTheory Set

universe u v

namespace ProfiniteGrp

/-- An element of a profinite group is a topological generator when its integral
powers have dense range. -/
def IsTopologicalGenerator (G : ProfiniteGrp.{u}) (g : G) : Prop :=
  DenseRange fun n : ℤ ↦ g ^ n

/-- A profinite group is procyclic when it has a topological generator. -/
def IsProcyclic (G : ProfiniteGrp.{u}) : Prop :=
  ∃ g : G, IsTopologicalGenerator G g

namespace IsTopologicalGenerator

variable {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}} {g : G}

/-- Topological generation expressed using the closure of the cyclic subgroup. -/
theorem iff_topologicalClosure_zpowers :
    IsTopologicalGenerator G g ↔ (Subgroup.zpowers g).topologicalClosure = ⊤ := by
  rw [IsTopologicalGenerator, SetLike.ext'_iff]
  simp only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, DenseRange,
    dense_iff_closure_eq, Subgroup.coe_zpowers]

/-- Topological generation expressed directly as a closure equality. -/
theorem iff_closure_range :
    IsTopologicalGenerator G g ↔ closure (range fun n : ℤ ↦ g ^ n) = univ :=
  denseRange_iff_closure_range

/-- The natural powers of a topological generator are also dense. -/
theorem denseRange_pow (hg : IsTopologicalGenerator G g) :
    DenseRange fun n : ℕ ↦ g ^ n :=
  denseRange_zpow_iff_pow.mp hg

/-- A surjective continuous homomorphism sends a topological generator to a
topological generator. -/
theorem map (hg : IsTopologicalGenerator G g) (f : G →ₜ* H)
    (hf : Function.Surjective f) : IsTopologicalGenerator H (f g) := by
  have hcomp : DenseRange (f ∘ fun n : ℤ ↦ g ^ n) :=
    hf.denseRange.comp hg f.continuous_toFun
  rw [IsTopologicalGenerator, show (fun n : ℤ ↦ f g ^ n) =
    f ∘ fun n : ℤ ↦ g ^ n by
      funext n
      exact (map_zpow f g n).symm]
  exact hcomp

/-- A continuous group equivalence preserves topological generators. -/
theorem map_equiv (hg : IsTopologicalGenerator G g) (e : G ≃ₜ* H) :
    IsTopologicalGenerator H (e g) :=
  hg.map (e : G →ₜ* H) e.surjective

/-- A continuous group equivalence reflects topological generators. -/
theorem equiv_iff (e : G ≃ₜ* H) :
    IsTopologicalGenerator H (e g) ↔ IsTopologicalGenerator G g := by
  constructor
  · intro h
    simpa using h.map_equiv e.symm
  · exact fun h ↦ h.map_equiv e

end IsTopologicalGenerator

/-- Every element of a subsingleton profinite group is a topological generator. -/
theorem isTopologicalGenerator_of_subsingleton (G : ProfiniteGrp.{u}) [Subsingleton G]
    (g : G) : IsTopologicalGenerator G g := by
  apply Function.Surjective.denseRange
  intro x
  exact ⟨0, Subsingleton.elim _ _⟩

/-- Every subsingleton profinite group is procyclic. -/
theorem isProcyclic_of_subsingleton (G : ProfiniteGrp.{u}) [Subsingleton G] :
    IsProcyclic G :=
  ⟨1, isTopologicalGenerator_of_subsingleton G 1⟩

/-- The standard one-element profinite group is procyclic. -/
theorem punit_isProcyclic :
    IsProcyclic (ofFiniteGrp (FiniteGrp.of PUnit)) := by
  change ∃ g : PUnit, DenseRange fun n : ℤ ↦ g ^ n
  refine ⟨PUnit.unit, Function.Surjective.denseRange ?_⟩
  intro x
  exact ⟨0, Subsingleton.elim _ _⟩

/-- Procyclicity is preserved and reflected by a continuous group equivalence. -/
theorem isProcyclic_iff_of_continuousMulEquiv (G : ProfiniteGrp.{u})
    (H : ProfiniteGrp.{v}) (e : G ≃ₜ* H) : IsProcyclic G ↔ IsProcyclic H := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨e g, hg.map_equiv e⟩
  · rintro ⟨h, hh⟩
    exact ⟨e.symm h, hh.map_equiv e.symm⟩

/-- A continuous quotient of a procyclic profinite group is procyclic. -/
theorem IsProcyclic.quotient {G H : ProfiniteGrp.{u}} (hG : IsProcyclic G)
    (f : G ⟶ H) (hf : Function.Surjective f) : IsProcyclic H := by
  obtain ⟨g, hg⟩ := hG
  exact ⟨f g, hg.map f.hom hf⟩

/-- The profinite completion of the infinite cyclic group, in any target
universe. -/
abbrev integerCompletion : ProfiniteGrp.{u} :=
  ProfiniteCompletion.completion (GrpCat.of (ULift.{u} (Multiplicative ℤ)))

/-- The homomorphism from the infinite cyclic group determined by `g`. -/
def integerPowerHom (G : ProfiniteGrp.{u}) (g : G) :
    GrpCat.of (ULift.{u} (Multiplicative ℤ)) ⟶ ↧G :=
  GrpCat.ofHom (uliftZPowersHom G g)

/-- The canonical continuous homomorphism from the profinite completion of the
integers which sends `1` to `g`. -/
noncomputable def integerCompletionMap (G : ProfiniteGrp.{u}) (g : G) :
    integerCompletion ⟶ G :=
  ProfiniteCompletion.lift (integerPowerHom G g)

/-- The canonical completion map extends integral exponentiation. -/
@[simp]
theorem integerCompletionMap_eta (G : ProfiniteGrp.{u}) (g : G)
    (n : ULift.{u} (Multiplicative ℤ)) :
    integerCompletionMap G g
        (ProfiniteCompletion.etaFn
          (GrpCat.of (ULift.{u} (Multiplicative ℤ))) n) =
      g ^ n.down.toAdd := by
  have h := ConcreteCategory.congr_hom
    (ProfiniteCompletion.lift_eta (integerPowerHom G g)) n
  change (ProfiniteCompletion.eta
      (GrpCat.of (ULift.{u} (Multiplicative ℤ))) ≫
        (forget₂ ProfiniteGrp GrpCat).map
          (ProfiniteCompletion.lift (integerPowerHom G g))) n = _
  rw [h]
  exact uliftZPowersHom_apply_apply G g n

/-- The value of the canonical completion map on the usual integral dense
subgroup. -/
theorem integerCompletionMap_eta_int (G : ProfiniteGrp.{u}) (g : G) (n : ℤ) :
    integerCompletionMap G g
        (ProfiniteCompletion.etaFn
          (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
          (ULift.up (Multiplicative.ofAdd n))) = g ^ n :=
  integerCompletionMap_eta G g _

/-- The closure of the range of the canonical completion map is the closure of
the integral powers of its distinguished element. -/
theorem closure_range_integerCompletionMap (G : ProfiniteGrp.{u}) (g : G) :
    closure (range (integerCompletionMap G g)) =
      closure (range fun n : ℤ ↦ g ^ n) := by
  let η := ProfiniteCompletion.etaFn
    (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
  let f : integerCompletion → G := integerCompletionMap G g
  have hη : closure (range η) = univ :=
    (ProfiniteCompletion.denseRange
      (GrpCat.of (ULift.{u} (Multiplicative ℤ)))).closure_range
  have h := closure_image_closure (s := range η)
    (integerCompletionMap G g).hom.continuous_toFun
  rw [hη, image_univ, ← range_comp] at h
  have hrange :
      range (fun n : ULift.{u} (Multiplicative ℤ) ↦ g ^ n.down.toAdd) =
        range (fun n : ℤ ↦ g ^ n) := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n.down.toAdd, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨ULift.up (Multiplicative.ofAdd n), rfl⟩
  have hfun : f ∘ η = fun n : ULift.{u} (Multiplicative ℤ) ↦
      g ^ n.down.toAdd := by
    funext n
    exact integerCompletionMap_eta G g n
  change closure (range f) = closure (range (f ∘ η)) at h
  rw [hfun, hrange] at h
  exact h

/-- The range of the canonical completion map is exactly the closure of the
integral powers.  Closedness here uses compactness of the completion and the
Hausdorff topology on the target. -/
theorem range_integerCompletionMap (G : ProfiniteGrp.{u}) (g : G) :
    range (integerCompletionMap G g) = closure (range fun n : ℤ ↦ g ^ n) := by
  have hclosed : IsClosed (range (integerCompletionMap G g)) :=
    (isCompact_range (integerCompletionMap G g).hom.continuous_toFun).isClosed
  rw [← closure_range_integerCompletionMap G g, hclosed.closure_eq]

/-- An element topologically generates exactly when its canonical map from the
profinite completion of the integers is surjective. -/
theorem isTopologicalGenerator_iff_surjective_integerCompletionMap
    (G : ProfiniteGrp.{u}) (g : G) :
    IsTopologicalGenerator G g ↔ Function.Surjective (integerCompletionMap G g) := by
  rw [IsTopologicalGenerator, DenseRange, dense_iff_closure_eq,
    ← range_integerCompletionMap G g]
  exact range_eq_univ

/-- The categorical form of the completion-map characterization. -/
theorem isTopologicalGenerator_iff_epi_integerCompletionMap
    (G : ProfiniteGrp.{u}) (g : G) :
    IsTopologicalGenerator G g ↔ Epi (integerCompletionMap G g) :=
  (isTopologicalGenerator_iff_surjective_integerCompletionMap G g).trans
    (epi_iff_surjective (integerCompletionMap G g)).symm

/-- A profinite group is procyclic exactly when one of its canonical maps from
the profinite completion of the integers is surjective. -/
theorem isProcyclic_iff_exists_surjective_integerCompletionMap
    (G : ProfiniteGrp.{u}) :
    IsProcyclic G ↔ ∃ g : G, Function.Surjective (integerCompletionMap G g) := by
  simp only [IsProcyclic,
    isTopologicalGenerator_iff_surjective_integerCompletionMap]

/-- The standard finite cyclic profinite group of order `n`. -/
abbrev finiteCyclic (n : ℕ) [NeZero n] : ProfiniteGrp :=
  ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod n)))

/-- The standard generator of `finiteCyclic n`. -/
abbrev finiteCyclicGenerator (n : ℕ) [NeZero n] : finiteCyclic n :=
  show Multiplicative (ZMod n) from Multiplicative.ofAdd (1 : ZMod n)

/-- The standard generator topologically generates the finite cyclic profinite
group. -/
theorem finiteCyclicGenerator_isTopologicalGenerator (n : ℕ) [NeZero n] :
    IsTopologicalGenerator (finiteCyclic n) (finiteCyclicGenerator n) := by
  apply Function.Surjective.denseRange
  intro x
  change Multiplicative (ZMod n) at x
  simp only [finiteCyclicGenerator]
  change ∃ k : ℤ, Multiplicative.ofAdd (1 : ZMod n) ^ k = x
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨k, Multiplicative.toAdd.injective ?_⟩
  simpa only [toAdd_zpow, toAdd_ofAdd, Int.smul_one_eq_cast] using hk

/-- Every standard finite cyclic profinite group is procyclic. -/
theorem finiteCyclic_isProcyclic (n : ℕ) [NeZero n] : IsProcyclic (finiteCyclic n) :=
  ⟨finiteCyclicGenerator n, finiteCyclicGenerator_isTopologicalGenerator n⟩

end ProfiniteGrp

namespace ProfiniteAddGrp

/-- An element of a profinite additive group is a topological generator when
its integral multiples have dense range. -/
def IsTopologicalGenerator (G : ProfiniteAddGrp.{u}) (g : G) : Prop :=
  DenseRange fun n : ℤ ↦ n • g

/-- A profinite additive group is procyclic when it has a topological
generator. -/
def IsProcyclic (G : ProfiniteAddGrp.{u}) : Prop :=
  ∃ g : G, IsTopologicalGenerator G g

namespace IsTopologicalGenerator

variable {G : ProfiniteAddGrp.{u}} {H : ProfiniteAddGrp.{v}} {g : G}

/-- Additive topological generation expressed using the closure of the cyclic
additive subgroup. -/
theorem iff_topologicalClosure_zmultiples :
    IsTopologicalGenerator G g ↔
      (AddSubgroup.zmultiples g).topologicalClosure = ⊤ := by
  rw [IsTopologicalGenerator, SetLike.ext'_iff]
  simp only [AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_top, DenseRange,
    dense_iff_closure_eq, AddSubgroup.coe_zmultiples]

/-- Additive topological generation expressed directly as a closure equality. -/
theorem iff_closure_range :
    IsTopologicalGenerator G g ↔ closure (range fun n : ℤ ↦ n • g) = univ :=
  denseRange_iff_closure_range

/-- The natural multiples of an additive topological generator are dense. -/
theorem denseRange_nsmul (hg : IsTopologicalGenerator G g) :
    DenseRange fun n : ℕ ↦ n • g :=
  denseRange_zsmul_iff_nsmul.mp hg

/-- A surjective continuous additive homomorphism sends a topological generator
to a topological generator. -/
theorem map (hg : IsTopologicalGenerator G g) (f : G →ₜ+ H)
    (hf : Function.Surjective f) : IsTopologicalGenerator H (f g) := by
  have hcomp : DenseRange (f ∘ fun n : ℤ ↦ n • g) :=
    hf.denseRange.comp hg f.continuous_toFun
  rw [IsTopologicalGenerator, show (fun n : ℤ ↦ n • f g) =
    f ∘ fun n : ℤ ↦ n • g by
      funext n
      exact (map_zsmul f n g).symm]
  exact hcomp

/-- A continuous additive equivalence preserves topological generators. -/
theorem map_equiv (hg : IsTopologicalGenerator G g) (e : G ≃ₜ+ H) :
    IsTopologicalGenerator H (e g) :=
  hg.map (e : G →ₜ+ H) e.surjective

/-- A continuous additive equivalence reflects topological generators. -/
theorem equiv_iff (e : G ≃ₜ+ H) :
    IsTopologicalGenerator H (e g) ↔ IsTopologicalGenerator G g := by
  constructor
  · intro h
    simpa using h.map_equiv e.symm
  · exact fun h ↦ h.map_equiv e

end IsTopologicalGenerator

/-- Every element of a subsingleton profinite additive group is a topological
generator. -/
theorem isTopologicalGenerator_of_subsingleton (G : ProfiniteAddGrp.{u})
    [Subsingleton G] (g : G) : IsTopologicalGenerator G g := by
  apply Function.Surjective.denseRange
  intro x
  exact ⟨0, Subsingleton.elim _ _⟩

/-- Every subsingleton profinite additive group is procyclic. -/
theorem isProcyclic_of_subsingleton (G : ProfiniteAddGrp.{u}) [Subsingleton G] :
    IsProcyclic G :=
  ⟨0, isTopologicalGenerator_of_subsingleton G 0⟩

/-- The standard one-element profinite additive group is procyclic. -/
theorem punit_isProcyclic :
    IsProcyclic (ofFiniteAddGrp (FiniteAddGrp.of PUnit)) := by
  change ∃ g : PUnit, DenseRange fun n : ℤ ↦ n • g
  refine ⟨PUnit.unit, Function.Surjective.denseRange ?_⟩
  intro x
  exact ⟨0, Subsingleton.elim _ _⟩

/-- Additive procyclicity is preserved and reflected by a continuous additive
equivalence. -/
theorem isProcyclic_iff_of_continuousAddEquiv (G : ProfiniteAddGrp.{u})
    (H : ProfiniteAddGrp.{v}) (e : G ≃ₜ+ H) : IsProcyclic G ↔ IsProcyclic H := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨e g, hg.map_equiv e⟩
  · rintro ⟨h, hh⟩
    exact ⟨e.symm h, hh.map_equiv e.symm⟩

/-- A continuous quotient of a procyclic profinite additive group is
procyclic. -/
theorem IsProcyclic.quotient {G H : ProfiniteAddGrp.{u}} (hG : IsProcyclic G)
    (f : G ⟶ H) (hf : Function.Surjective f) : IsProcyclic H := by
  obtain ⟨g, hg⟩ := hG
  exact ⟨f g, hg.map f.hom hf⟩

/-- The standard finite cyclic profinite additive group of order `n`. -/
abbrev finiteCyclic (n : ℕ) [NeZero n] : ProfiniteAddGrp :=
  ofFiniteAddGrp (FiniteAddGrp.of (ZMod n))

/-- The standard generator of the additive `finiteCyclic n`. -/
abbrev finiteCyclicGenerator (n : ℕ) [NeZero n] : finiteCyclic n :=
  show ZMod n from 1

/-- The standard additive generator topologically generates the finite cyclic
profinite additive group. -/
theorem finiteCyclicGenerator_isTopologicalGenerator (n : ℕ) [NeZero n] :
    IsTopologicalGenerator (finiteCyclic n) (finiteCyclicGenerator n) := by
  apply Function.Surjective.denseRange
  intro x
  change ZMod n at x
  simp only [finiteCyclicGenerator]
  change ∃ k : ℤ, k • (1 : ZMod n) = x
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective x
  refine ⟨k, ?_⟩
  rw [Int.smul_one_eq_cast]
  exact hk

/-- Every standard finite cyclic profinite additive group is procyclic. -/
theorem finiteCyclic_isProcyclic (n : ℕ) [NeZero n] : IsProcyclic (finiteCyclic n) :=
  ⟨finiteCyclicGenerator n, finiteCyclicGenerator_isTopologicalGenerator n⟩

end ProfiniteAddGrp
