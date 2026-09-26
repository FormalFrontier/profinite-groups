/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# Free products of profinite groups

This file constructs free products of profinite groups by completing the
abstract free product with respect to exactly those finite quotients whose
restriction to every factor is continuous.

The family and the target of the universal lift carry their stated universe
and profiniteness assumptions. The construction does not use an abstract
free product with its unmodified quotient topology.

## Using the universal property

For `G : ι → ProfiniteGrp`, use `product G` for the free profinite product and
`of G i` for its continuous factor maps. A family `f` of continuous homomorphisms
to a profinite target in universe `max u v` extends by `lift f`; `lift_of` computes
its restriction to a factor, and `hom_ext` proves equality of maps by checking
those restrictions. `homEquiv` packages this correspondence, with inverse `lift`.

The map `eta` instead starts from the *abstract* free product and has dense range;
`lift_eta` is its computation rule after forgetting topology. For changing the
factors, use `map` with `map_of`, `map_id` and `map_comp`. The factor maps are
injective by `of_injective`, and their images topologically generate the product
by `factors_topologically_generate`.
-/

@[expose] public section

universe u v

open CategoryTheory Filter

namespace ProfiniteGrp.FreeProduct

variable {ι : Type v} (G : ι → ProfiniteGrp.{u})

/-- The abstract free product of the underlying groups. -/
abbrev Abstract : Type max u v :=
  @Monoid.CoprodI.{v, u} ι (fun i ↦ G i) (fun i ↦ (G i).group.toMonoid)

/-- A finite quotient of the abstract free product is admissible when its
restriction to every profinite factor is continuous. Openness of the kernels
is the convenient finite-discrete formulation of this condition. -/
@[ext]
structure AdmissibleQuotient extends FiniteIndexNormalSubgroup (Abstract G) where
  isOpen_comap' (i : ι) : IsOpen
    (((toFiniteIndexNormalSubgroup.toSubgroup.comap
      (Monoid.CoprodI.of (M := fun j ↦ G j) : G i →* Abstract G)) :
        Subgroup (G i)) : Set (G i))

namespace AdmissibleQuotient

/-- An admissible quotient is determined by its underlying finite-index normal
subgroup; the openness certificates introduce no additional choice of quotient. -/
theorem toFiniteIndexNormalSubgroup_injective : Function.Injective
    (toFiniteIndexNormalSubgroup : AdmissibleQuotient G →
      FiniteIndexNormalSubgroup (Abstract G)) := by
  rintro ⟨U, hU⟩ ⟨V, hV⟩ h
  cases h
  rfl

instance : PartialOrder (AdmissibleQuotient G) :=
  PartialOrder.lift toFiniteIndexNormalSubgroup
    (toFiniteIndexNormalSubgroup_injective G)

/-- Common refinement of two finite admissible quotients. Intersecting their
kernels preserves openness after restriction to every profinite factor. -/
def inf (U V : AdmissibleQuotient G) : AdmissibleQuotient G :=
  { toFiniteIndexNormalSubgroup :=
      U.toFiniteIndexNormalSubgroup ⊓ V.toFiniteIndexNormalSubgroup
    isOpen_comap' := fun i ↦ by
      convert (U.isOpen_comap' i).inter (V.isOpen_comap' i) using 1
      ext x
      change
        (Monoid.CoprodI.of (M := fun j ↦ G j) x ∈
            U.toFiniteIndexNormalSubgroup.toSubgroup ∧
          Monoid.CoprodI.of (M := fun j ↦ G j) x ∈
            V.toFiniteIndexNormalSubgroup.toSubgroup) ↔ _
      rfl }

instance : SemilatticeInf (AdmissibleQuotient G) where
  inf := inf G
  inf_le_left U V := show
    U.toFiniteIndexNormalSubgroup ⊓ V.toFiniteIndexNormalSubgroup ≤
      U.toFiniteIndexNormalSubgroup from inf_le_left
  inf_le_right U V := show
    U.toFiniteIndexNormalSubgroup ⊓ V.toFiniteIndexNormalSubgroup ≤
      V.toFiniteIndexNormalSubgroup from inf_le_right
  le_inf U V W hUV hUW := show U.toFiniteIndexNormalSubgroup ≤
      V.toFiniteIndexNormalSubgroup ⊓ W.toFiniteIndexNormalSubgroup from
    le_inf hUV hUW

/-- The indiscrete quotient is admissible. -/
def top : AdmissibleQuotient G where
  toFiniteIndexNormalSubgroup :=
    FiniteIndexNormalSubgroup.ofSubgroup (⊤ : Subgroup (Abstract G))
  isOpen_comap' := fun _ ↦ by simp

instance : Nonempty (AdmissibleQuotient G) := ⟨top G⟩

end AdmissibleQuotient

/-- The diagram of admissible finite quotients of the abstract free product. -/
def finiteGrpDiagram : AdmissibleQuotient G ⥤ FiniteGrp.{max u v} where
  obj U := ↧(Abstract G ⧸ U.toFiniteIndexNormalSubgroup.toSubgroup)
  map f := FiniteGrp.ofHom <| QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id U := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

/-- The admissible finite-quotient diagram viewed in profinite groups. -/
def diagram : AdmissibleQuotient G ⥤ ProfiniteGrp.{max u v} :=
  finiteGrpDiagram G ⋙ forget₂ _ _

/-- The free profinite product, as the limit of its admissible finite
quotients. -/
def product : ProfiniteGrp.{max u v} := limit (diagram G)

/-- The canonical map from the abstract free product to the free profinite
product, as a function. Its range will be shown to be dense. -/
def etaFn (x : Abstract G) : product G :=
  ⟨fun _ ↦ QuotientGroup.mk x, fun _ _ _ ↦ rfl⟩

/-- The canonical homomorphism from the abstract free product to the
underlying group of the free profinite product. -/
def eta : GrpCat.of (Abstract G) ⟶ ↧(product G) := GrpCat.ofHom {
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
}

set_option backward.isDefEq.respectTransparency false in
/-- The abstract free product has dense image in its admissible finite-quotient
completion. -/
theorem denseRange : DenseRange (etaFn G) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsOpen, hs⟩ ⟨⟨spc, hspc⟩, hmem⟩
  rw [← hs, Set.mem_preimage] at hmem
  rcases (isOpen_pi_iff.mp hsOpen) _ hmem with ⟨J, fJ, hJ1, hJ2⟩
  let N : Subgroup (Abstract G) :=
    iInf fun j : J ↦ j.val.toFiniteIndexNormalSubgroup.toSubgroup
  have hNNormal : N.Normal := Subgroup.normal_iInf_normal fun j ↦ inferInstance
  have hNFinite : N.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  let m : AdmissibleQuotient G :=
    { toFiniteIndexNormalSubgroup :=
        { toSubgroup := N
          isNormal' := hNNormal
          isFiniteIndex' := hNFinite }
      isOpen_comap' := fun i ↦ by
        rw [show
          (((N.comap
            (Monoid.CoprodI.of (M := fun j ↦ G j) : G i →* Abstract G)) :
              Subgroup (G i)) : Set (G i)) =
            ⋂ j : J,
              ((j.val.toFiniteIndexNormalSubgroup.toSubgroup.comap
                (Monoid.CoprodI.of (M := fun k ↦ G k) : G i →* Abstract G) :
                  Subgroup (G i)) : Set (G i)) by
            ext x
            simp [N]]
        exact isOpen_iInter_of_finite fun j ↦ j.val.isOpen_comap' i }
  rcases QuotientGroup.mk'_surjective N (spc m) with ⟨origin, horigin⟩
  use etaFn G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hs]
  apply hJ2
  intro a ha
  let mToA : m ⟶ a :=
    (iInf_le (fun j : J ↦
      j.val.toFiniteIndexNormalSubgroup.toSubgroup) ⟨a, ha⟩).hom
  rw [← (etaFn G origin).property mToA]
  dsimp [etaFn] at ⊢ horigin
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc mToA) (hJ1 a ha).2

/-- The canonical continuous inclusion of a factor into the free profinite
product. -/
def of (i : ι) : G i →ₜ* product G where
  toFun x := etaFn G (Monoid.CoprodI.of (M := fun j ↦ G j) x)
  map_one' := map_one ((eta G).hom.comp
    (Monoid.CoprodI.of (M := fun j ↦ G j)))
  map_mul' _ _ := map_mul ((eta G).hom.comp
    (Monoid.CoprodI.of (M := fun j ↦ G j))) _ _
  continuous_toFun := by
    apply continuous_induced_rng.mpr (continuous_pi _)
    intro U
    let q : G i →* (diagram G).obj U :=
      (QuotientGroup.mk' U.toFiniteIndexNormalSubgroup.toSubgroup).comp
        (Monoid.CoprodI.of (M := fun j ↦ G j))
    have hq : q.ker = U.toFiniteIndexNormalSubgroup.toSubgroup.comap
        (Monoid.CoprodI.of (M := fun j ↦ G j) : G i →* Abstract G) := by
      ext x
      exact QuotientGroup.eq_one_iff
        (N := U.toFiniteIndexNormalSubgroup.toSubgroup)
        (Monoid.CoprodI.of (M := fun j ↦ G j) x)
    have hqOpen : IsOpen (q.ker : Set (G i)) := by
      rw [hq]
      exact U.isOpen_comap' i
    let _ : DiscreteTopology ((diagram G).obj U) := ⟨rfl⟩
    change Continuous q
    apply continuous_of_continuousAt_one q
    rw [ContinuousAt, nhds_discrete ((diagram G).obj U), map_one, tendsto_pure]
    change {x | q x = 1} ∈ nhds (1 : G i)
    rw [show {x | q x = 1} = (q.ker : Set (G i)) by ext x; simp]
    exact hqOpen.mem_nhds q.ker.one_mem

variable {G}
variable {P : ProfiniteGrp.{max u v}}

/-- The abstract homomorphism out of the free product induced by a family of
continuous homomorphisms. -/
def abstractLift (f : ∀ i, G i →ₜ* P) : Abstract G →* P :=
  Monoid.CoprodI.lift fun i ↦ (f i).toMonoidHom

/-- An abstract lift agrees with its continuous input on each factor. -/
@[simp]
theorem abstractLift_of (f : ∀ i, G i →ₜ* P) (i : ι) (x : G i) :
    abstractLift f (Monoid.CoprodI.of (M := fun j ↦ G j) x) = f i x := by
  simp [abstractLift]

/-- Pulling an open normal subgroup of the target back along the abstract
lift gives an admissible finite quotient. -/
def preimage (f : ∀ i, G i →ₜ* P) (H : OpenNormalSubgroup P) :
    AdmissibleQuotient G where
  toFiniteIndexNormalSubgroup :=
    H.toFiniteIndexNormalSubgroup.comap (abstractLift f)
  isOpen_comap' i := by
    convert H.isOpen'.preimage (f i).continuous_toFun using 1
    ext x
    change abstractLift f (Monoid.CoprodI.of (M := fun j ↦ G j) x) ∈ H ↔
      f i x ∈ H
    rw [abstractLift_of]

/-- Target quotient refinements induce source-side admissible refinements. -/
theorem preimage_le {f : ∀ i, G i →ₜ* P} {H K : OpenNormalSubgroup P}
    (h : H ≤ K) : preimage f H ≤ preimage f K :=
  FiniteIndexNormalSubgroup.comap_mono (abstractLift f)
    (OpenNormalSubgroup.toFiniteIndexNormalSubgroup_mono h)

/-- The finite quotient map induced by a family of continuous homomorphisms. -/
def quotientMap (f : ∀ i, G i →ₜ* P) (H : OpenNormalSubgroup P) :
    FiniteGrp.of (Abstract G ⧸
      (preimage f H).toFiniteIndexNormalSubgroup.toSubgroup) ⟶
      FiniteGrp.of (P ⧸ H.toSubgroup) :=
  FiniteGrp.ofHom <| QuotientGroup.map _ _ (abstractLift f) fun _ h ↦ h

/-- The continuous homomorphism from the free profinite product induced by a
family of continuous homomorphisms. -/
noncomputable def lift (f : ∀ i, G i →ₜ* P) : product G ⟶ P :=
  P.isLimitCone.lift ⟨_, {
    app H := (limitCone (diagram G)).π.app (preimage f H) ≫
      (ofFiniteGrpHom <| quotientMap f H)
    naturality := by
      intro X Y g
      ext ⟨x, hx⟩
      change quotientMap f Y (x <| preimage f Y) =
        P.diagram.map g (quotientMap f X (x <| preimage f X))
      have hxy := hx (preimage_le (f := f) g.le).hom
      obtain ⟨t, ht⟩ : ∃ t : Abstract G,
          QuotientGroup.mk t = x (preimage f X) :=
        QuotientGroup.mk_surjective (x (preimage f X))
      rw [← hxy, ← ht]
      have hp := P.cone.π.naturality g
      apply_fun fun q ↦ q (abstractLift f t) at hp
      exact hp
  }⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- On the dense abstract free product, the continuous universal lift agrees
with `abstractLift`. The equation is in groups after forgetting topology. -/
@[reassoc (attr := simp)]
theorem lift_eta (f : ∀ i, G i →ₜ* P) :
    eta G ≫ (forget₂ _ _).map (lift f) = GrpCat.ofHom (abstractLift f) := by
  let e := isoLimittoFiniteQuotientFunctor P
  rw [← (forget₂ ProfiniteGrp GrpCat).mapIso e |>.cancel_iso_hom_right]
  dsimp
  rw [Category.assoc, ← (forget₂ ProfiniteGrp GrpCat).map_comp (lift f) e.hom]
  change eta G ≫ ((forget₂ _ _).map ((_ ≫ e.inv) ≫ e.hom)) = _
  simp only [Category.assoc, Iso.inv_hom_id]
  rfl

/-- Two maps from the free profinite product that agree on the dense abstract
free product are equal. -/
theorem lift_unique (f g : product G ⟶ P)
    (h : eta G ≫ (forget₂ _ _).map f =
      eta G ≫ (forget₂ _ _).map g) : f = g := by
  ext x
  apply congrFun
  refine (denseRange G).equalizer f.hom.continuous_toFun
    g.hom.continuous_toFun ?_
  funext y
  simpa [GrpCat.comp_apply] using! (ConcreteCategory.congr_hom h y)

/-- The free profinite universal lift restricts to each specified continuous
factor map; this is the computation rule for the universal construction. -/
@[simp]
theorem lift_of (f : ∀ i, G i →ₜ* P) (i : ι) :
    (lift f).hom.comp (of G i) = f i := by
  ext x
  change (lift f).hom
      (etaFn G (Monoid.CoprodI.of (M := fun j ↦ G j) x)) = f i x
  rw [← abstractLift_of f i x]
  simpa only [GrpCat.comp_apply] using!
    (ConcreteCategory.congr_hom (lift_eta f)
      (Monoid.CoprodI.of (M := fun j ↦ G j) x))

variable (G)

/-- A factor, lifted to the universe of the free product. -/
private def liftedFactor (i : ι) : ProfiniteGrp.{max u v} :=
  ProfiniteGrp.ofContinuousMulEquiv (G := G i) (H := ULift.{v} (G i))
    { toFun := ULift.up
      invFun := ULift.down
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_uliftUp
      continuous_invFun := continuous_uliftDown }

private def factorUp (i : ι) : G i →ₜ* liftedFactor G i where
  toFun := ULift.up
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_uliftUp

private def trivialToFactor (i j : ι) : G j →ₜ* liftedFactor G i where
  toFun _ := 1
  map_one' := rfl
  map_mul' _ _ := by simp
  continuous_toFun := continuous_const

private noncomputable def factorRetraction (i : ι) :
    product G ⟶ liftedFactor G i := by
  classical
  exact lift (Function.update (trivialToFactor G i) i (factorUp G i))

@[simp]
private theorem factorRetraction_of (i : ι) :
    (factorRetraction G i).hom.comp (of G i) = factorUp G i := by
  classical
  rw [factorRetraction, lift_of]
  exact Function.update_self i (factorUp G i) (trivialToFactor G i)

/-- Every factor embeds in the free profinite product. -/
theorem of_injective (i : ι) : Function.Injective (of G i) := by
  intro x y hxy
  have hleft := DFunLike.congr_fun (factorRetraction_of G i) x
  have hright := DFunLike.congr_fun (factorRetraction_of G i) y
  have h : factorUp G i x = factorUp G i y := by
    rw [← hleft, ← hright]
    exact congrArg (factorRetraction G i) hxy
  exact congrArg ULift.down h

/-- The images of the factors topologically generate the free profinite
product. -/
theorem factors_topologically_generate :
    (⨆ i, (of G i).toMonoidHom.range).topologicalClosure = ⊤ := by
  rw [← Monoid.CoprodI.range_eq_iSup]
  have hLift : Monoid.CoprodI.lift (fun i ↦ (of G i).toMonoidHom) =
      (eta G).hom := by
    apply Monoid.CoprodI.ext_hom
    intro i
    ext x
    rfl
  rw [hLift]
  apply SetLike.coe_injective
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_top]
  change closure (Set.range (etaFn G)) = Set.univ
  exact (denseRange G).closure_eq

variable {G}

/-- Morphisms out of the free profinite product are determined by their
restrictions to the factors. -/
@[ext]
theorem hom_ext (f g : product G ⟶ P)
    (h : ∀ i, f.hom.comp (of G i) = g.hom.comp (of G i)) : f = g := by
  apply lift_unique
  apply GrpCat.hom_ext
  apply Monoid.CoprodI.ext_hom
  intro i
  ext x
  simpa [GrpCat.comp_apply, of] using! DFunLike.congr_fun (h i) x

variable {Q : ProfiniteGrp.{max u v}}

/-- The universal lift is natural in the profinite target. -/
@[reassoc]
theorem lift_comp (f : ∀ i, G i →ₜ* P) (g : P ⟶ Q) :
    lift f ≫ g = lift fun i ↦ g.hom.comp (f i) := by
  apply hom_ext
  intro i
  change g.hom.comp ((lift f).hom.comp (of G i)) =
    (lift fun i ↦ g.hom.comp (f i)).hom.comp (of G i)
  rw [lift_of, lift_of]

/-- Continuous homomorphisms out of the free profinite product are equivalent
to families of continuous homomorphisms out of its factors. -/
noncomputable def homEquiv : (product G ⟶ P) ≃ (∀ i, G i →ₜ* P) where
  toFun f i := f.hom.comp (of G i)
  invFun := lift
  left_inv f := by
    apply hom_ext
    intro i
    exact lift_of (fun j ↦ f.hom.comp (of G j)) i
  right_inv f := funext fun i ↦ lift_of f i

/-- The forward universal-property correspondence restricts a morphism to
the indicated factor via its canonical continuous map. -/
@[simp]
theorem homEquiv_apply (f : product G ⟶ P) (i : ι) :
    homEquiv f i = f.hom.comp (of G i) := rfl

/-- The inverse universal-property correspondence extends the supplied family
by the continuous universal lift. -/
@[simp]
theorem homEquiv_symm_apply (f : ∀ i, G i →ₜ* P) :
    homEquiv.symm f = lift f := rfl

/-- The free profinite product of an empty family is initial. -/
noncomputable def emptyIsInitial (G : ι → ProfiniteGrp.{u}) [IsEmpty ι] :
    Limits.IsInitial (product G) :=
  Limits.IsInitial.ofUniqueHom (fun _ ↦ lift fun i ↦ isEmptyElim i) fun _ f ↦ by
    apply hom_ext
    intro i
    exact isEmptyElim i

/-- The free profinite product of a singleton family is its unique factor. -/
noncomputable def punitIso (P : ProfiniteGrp.{u}) :
    product (fun _ : PUnit ↦ P) ≅ P where
  hom := lift fun _ ↦ ContinuousMonoidHom.id P
  inv := ProfiniteGrp.ofHom (of (fun _ : PUnit ↦ P) PUnit.unit)
  hom_inv_id := by
    apply hom_ext
    intro i
    obtain rfl := Subsingleton.elim i PUnit.unit
    ext x
    change of (fun _ : PUnit ↦ P) PUnit.unit
      ((lift fun _ : PUnit ↦ ContinuousMonoidHom.id P)
        (of (fun _ : PUnit ↦ P) PUnit.unit x)) =
        of (fun _ : PUnit ↦ P) PUnit.unit x
    rw [show (lift (fun _ : PUnit ↦ ContinuousMonoidHom.id P)).hom
        (of (fun _ : PUnit ↦ P) PUnit.unit x) = x by
      exact DFunLike.congr_fun (lift_of (fun _ : PUnit ↦ ContinuousMonoidHom.id P)
        PUnit.unit) x]
  inv_hom_id := by
    ext x
    exact DFunLike.congr_fun
      (lift_of (fun _ : PUnit ↦ ContinuousMonoidHom.id P) PUnit.unit) x

variable {κ : Type v}

/-- Reindexing a family along an equivalence does not change its free
profinite product. -/
noncomputable def reindexIso (G : ι → ProfiniteGrp.{u}) (e : κ ≃ ι) :=
  let invFamily : ∀ i, G i →ₜ* product (fun k ↦ G (e k)) := fun i ↦
    (of (fun k ↦ G (e k)) (e.symm i)).comp
      (eqToHom (congrArg G (e.apply_symm_apply i).symm)).hom
  let ofCompEqToHom : ∀ {α : Type v} (F : α → ProfiniteGrp.{u})
      {i j : α} (h : i = j),
      (of F j).comp (eqToHom (congrArg F h)).hom = of F i := by
    intro α F i j h
    subst j
    rfl
  show product (fun k ↦ G (e k)) ≅ product G from {
  hom := lift fun k ↦ of G (e k)
  inv := lift invFamily
  hom_inv_id := by
    apply hom_ext
    intro k
    change (lift invFamily).hom.comp
      ((lift fun k ↦ of G (e k)).hom.comp (of (fun k ↦ G (e k)) k)) =
        of (fun k ↦ G (e k)) k
    rw [lift_of, lift_of]
    simpa only [invFamily] using (show
      (of (fun k ↦ G (e k)) (e.symm (e k))).comp
          (eqToHom (congrArg G (e.apply_symm_apply (e k)).symm)).hom =
        of (fun k ↦ G (e k)) k from by
      simpa using ofCompEqToHom (fun k ↦ G (e k)) (e.symm_apply_apply k).symm)
  inv_hom_id := by
    apply hom_ext
    intro i
    change (lift fun k ↦ of G (e k)).hom.comp
      ((lift invFamily).hom.comp (of G i)) = of G i
    rw [lift_of]
    dsimp only [invFamily]
    change ((lift fun k ↦ of G (e k)).hom.comp
      (of (fun k ↦ G (e k)) (e.symm i))).comp
        (eqToHom (congrArg G (e.apply_symm_apply i).symm)).hom = of G i
    rw [lift_of]
    exact ofCompEqToHom G (e.apply_symm_apply i).symm
  }

/-- Reindexing by an equivalence carries the new factor inclusion to the
corresponding original factor inclusion. -/
@[simp]
theorem reindexIso_hom_of (e : κ ≃ ι) (k : κ) :
    (reindexIso G e).hom.hom.comp (of (fun k ↦ G (e k)) k) = of G (e k) :=
  lift_of _ k

variable (G)
variable {H : ι → ProfiniteGrp.{u}} {K : ι → ProfiniteGrp.{u}}

/-- A family of continuous homomorphisms induces a homomorphism of free
profinite products. -/
noncomputable def map (f : ∀ i, G i →ₜ* H i) : product G ⟶ product H :=
  lift fun i ↦ (of H i).comp (f i)

/-- The map induced by a family of homomorphisms agrees with that family on
each factor, followed by the target's canonical factor map. -/
@[simp]
theorem map_of (f : ∀ i, G i →ₜ* H i) (i : ι) :
    (map G f).hom.comp (of G i) = (of H i).comp (f i) :=
  lift_of _ i

/-- Identity maps on the factors induce the identity on the free profinite
product, without unfolding its finite-quotient construction. -/
@[simp]
theorem map_id :
    map G (fun i ↦ ContinuousMonoidHom.id (G i)) = 𝟙 (product G) := by
  apply hom_ext
  intro i
  rw [map_of]
  rfl

/-- Mapping the factors twice agrees with mapping their componentwise
composites; categorical composition applies the left-hand map first. -/
@[simp]
theorem map_comp (f : ∀ i, G i →ₜ* H i) (g : ∀ i, H i →ₜ* K i) :
    map G f ≫ map H g = map G (fun i ↦ (g i).comp (f i)) := by
  apply hom_ext
  intro i
  ext x
  change (map H g).hom ((map G f).hom (of G i x)) =
    (map G (fun i ↦ (g i).comp (f i))).hom (of G i x)
  rw [show (map G f).hom (of G i x) = of H i (f i x) by
    exact DFunLike.congr_fun (map_of G f i) x]
  rw [show (map H g).hom (of H i (f i x)) = of K i (g i (f i x)) by
    exact DFunLike.congr_fun (map_of H g i) (f i x)]
  rw [show (map G (fun i ↦ (g i).comp (f i))).hom (of G i x) =
      of K i (g i (f i x)) by
    exact DFunLike.congr_fun (map_of G (fun i ↦ (g i).comp (f i)) i) x]

end ProfiniteGrp.FreeProduct
