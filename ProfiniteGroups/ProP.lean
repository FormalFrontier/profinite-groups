/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.FreeProduct
public import Mathlib.GroupTheory.PGroup

/-!
# Pro-`p` groups and maximal pro-`p` quotients

This file characterizes a pro-`p` group by its finite continuous quotients
and constructs the maximal pro-`p` quotient of an arbitrary profinite group.

It also constructs free pro-`p` products using the continuous free profinite
product. The universal maps retain the explicit prime and group assumptions
of their declarations.

## Using the quotient and product APIs

Supply `[Fact p.Prime]` when using the pro-`p` classes. In
`MaximalProPQuotient`, `eta p G` is the surjective map to `product p G`.
For a pro-`p` target `P`, `lift p f` factors a continuous homomorphism `f`
through this quotient; `lift_eta` computes the composite, and `lift_unique`
proves uniqueness. `homEquiv` packages the correspondence. `map` and `eta_map`
make the quotient construction natural in `G`.

In `FreeProPProduct`, the factors may initially be arbitrary profinite groups.
For a pro-`p` target in universe `max u v`, use `lift`, `lift_of` and `hom_ext`
to construct, compute and compare maps out of their product. Unlike the free
profinite product, injectivity of the factor maps here is asserted by
`of_injective` only under `[∀ i, IsProP p (G i)]`. Neither construction
requires a finite indexing family.
-/

@[expose] public section

universe u v

open CategoryTheory Filter

namespace IsPGroup

/-- A product of two `p`-groups is a `p`-group. -/
theorem prod {p : ℕ} {G H : Type*} [Group G] [Group H]
    (hG : IsPGroup p G) (hH : IsPGroup p H) : IsPGroup p (G × H) := by
  rintro ⟨g, h⟩
  obtain ⟨m, hm⟩ := hG g
  obtain ⟨n, hn⟩ := hH h
  refine ⟨m + n, ?_⟩
  apply Prod.ext
  · change g ^ (p ^ (m + n)) = 1
    rw [Nat.pow_add, pow_mul, hm, one_pow]
  · change h ^ (p ^ (m + n)) = 1
    rw [Nat.pow_add, mul_comm, pow_mul, hn, one_pow]

end IsPGroup

namespace ProfiniteGrp

/-- A profinite group is pro-`p` when every quotient by an open normal
subgroup is a finite `p`-group. -/
class IsProP (p : ℕ) (G : ProfiniteGrp.{u}) [Fact p.Prime] : Prop where
  quotient_isPGroup (U : OpenNormalSubgroup G) :
    IsPGroup p (G ⧸ U.toSubgroup)

namespace IsProP

variable {p : ℕ} [Fact p.Prime] {G : ProfiniteGrp.{u}}

/-- Extract the defining `p`-group property of a quotient by an open normal
subgroup from a supplied proof that the profinite group is pro-`p`. -/
theorem quotient (hG : IsProP p G) (U : OpenNormalSubgroup G) :
    IsPGroup p (G ⧸ U.toSubgroup) :=
  hG.quotient_isPGroup U

/-- An algebraic `p`-group with a profinite topology is pro-`p`. -/
theorem of_isPGroup (hG : IsPGroup p G) : IsProP p G where
  quotient_isPGroup U := hG.to_quotient U.toSubgroup

/-- The pro-`p` property is preserved by a continuous group equivalence. -/
theorem of_continuousMulEquiv {H : ProfiniteGrp.{v}} (hG : IsProP p G)
    (e : G ≃ₜ* H) : IsProP p H where
  quotient_isPGroup U := by
    let V : OpenNormalSubgroup G :=
      { toSubgroup := U.toSubgroup.comap e.toMonoidHom
        isOpen' := U.isOpen'.preimage e.continuous_toFun }
    let q : (G ⧸ V.toSubgroup) →* (H ⧸ U.toSubgroup) :=
      QuotientGroup.map _ _ e.toMonoidHom fun _ hx ↦ hx
    apply (hG.quotient V).of_surjective q
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup z
    refine ⟨QuotientGroup.mk (e.symm y), ?_⟩
    change QuotientGroup.mk (e (e.symm y)) = QuotientGroup.mk y
    rw [e.apply_symm_apply]

end IsProP

namespace MaximalProPQuotient

variable (p : ℕ) [Fact p.Prime] (G : ProfiniteGrp.{u})

/-- An open normal subgroup whose quotient is a `p`-group. -/
@[ext]
structure Quotient extends OpenNormalSubgroup G where
  isPGroup' : IsPGroup p (G ⧸ toOpenNormalSubgroup.toSubgroup)

namespace Quotient

omit [Fact p.Prime] in
/-- A finite `p`-group quotient kernel is determined by its underlying open
normal subgroup; its `p`-group certificate is proof-irrelevant. -/
theorem toOpenNormalSubgroup_injective : Function.Injective
    (toOpenNormalSubgroup : Quotient p G → OpenNormalSubgroup G) := by
  rintro ⟨U, hU⟩ ⟨V, hV⟩ h
  cases h
  rfl

instance : PartialOrder (Quotient p G) :=
  PartialOrder.lift toOpenNormalSubgroup
    (toOpenNormalSubgroup_injective p G)

omit [Fact p.Prime] in
/-- Intersecting two defining kernels still gives a `p`-group quotient: it
embeds in the product of the two original quotients. This supplies `Quotient.inf`. -/
theorem quotient_inf_isPGroup (U V : Quotient p G) :
    IsPGroup p (G ⧸
      (U.toOpenNormalSubgroup ⊓ V.toOpenNormalSubgroup).toSubgroup) := by
  let f : G →* (G ⧸ U.toOpenNormalSubgroup.toSubgroup) ×
      (G ⧸ V.toOpenNormalSubgroup.toSubgroup) :=
    (QuotientGroup.mk' U.toOpenNormalSubgroup.toSubgroup).prod
      (QuotientGroup.mk' V.toOpenNormalSubgroup.toSubgroup)
  have hprod : IsPGroup p ((G ⧸ U.toOpenNormalSubgroup.toSubgroup) ×
      (G ⧸ V.toOpenNormalSubgroup.toSubgroup)) :=
    U.isPGroup'.prod V.isPGroup'
  have hrange : IsPGroup p f.range := hprod.to_subgroup f.range
  have hker : f.ker =
      (U.toOpenNormalSubgroup ⊓ V.toOpenNormalSubgroup).toSubgroup := by
    dsimp only [f]
    rw [MonoidHom.ker_prod, QuotientGroup.ker_mk',
      QuotientGroup.ker_mk']
    rfl
  have hquot : IsPGroup p (G ⧸ f.ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  exact hquot.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)

/-- Intersections of pro-`p` quotient kernels are again pro-`p` quotient
kernels. -/
def inf (U V : Quotient p G) : Quotient p G where
  toOpenNormalSubgroup := U.toOpenNormalSubgroup ⊓ V.toOpenNormalSubgroup
  isPGroup' := quotient_inf_isPGroup p G U V

instance : SemilatticeInf (Quotient p G) where
  inf := inf p G
  inf_le_left U V := show
    U.toOpenNormalSubgroup ⊓ V.toOpenNormalSubgroup ≤
      U.toOpenNormalSubgroup from inf_le_left
  inf_le_right U V := show
    U.toOpenNormalSubgroup ⊓ V.toOpenNormalSubgroup ≤
      V.toOpenNormalSubgroup from inf_le_right
  le_inf U V W hUV hUW := show U.toOpenNormalSubgroup ≤
      V.toOpenNormalSubgroup ⊓ W.toOpenNormalSubgroup from le_inf hUV hUW

/-- The whole group as an open normal subgroup. -/
def topOpenNormal : OpenNormalSubgroup G where
  toSubgroup := ⊤
  isOpen' := isOpen_univ

/-- The trivial quotient is a `p`-group quotient. -/
def top : Quotient p G where
  toOpenNormalSubgroup := topOpenNormal G
  isPGroup' := by
    change IsPGroup p (G ⧸ (⊤ : Subgroup G))
    let _ : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
      QuotientGroup.subsingleton_quotient_top
    exact IsPGroup.of_subsingleton p (G ⧸ (⊤ : Subgroup G))

instance : Nonempty (Quotient p G) := ⟨top p G⟩

instance : OrderTop (Quotient p G) where
  top := top p G
  le_top U := show
      U.toOpenNormalSubgroup ≤ (top p G).toOpenNormalSubgroup from by
    intro x hx
    change x ∈ (⊤ : Subgroup G)
    trivial

end Quotient

/-- The diagram of finite `p`-group quotients of a profinite group. -/
def finiteGrpDiagram : Quotient p G ⥤ FiniteGrp.{u} where
  obj U := ↧(G ⧸ U.toOpenNormalSubgroup.toSubgroup)
  map f := FiniteGrp.ofHom <| QuotientGroup.map _ _
    (MonoidHom.id G) f.le
  map_id U := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

/-- The finite `p`-group quotient diagram viewed in profinite groups. -/
def diagram : Quotient p G ⥤ ProfiniteGrp.{u} :=
  finiteGrpDiagram p G ⋙ forget₂ _ _

/-- The maximal pro-`p` quotient, constructed as the limit of all finite
`p`-group quotients. -/
def product : ProfiniteGrp.{u} := limit (diagram p G)

/-- The canonical map to the maximal pro-`p` quotient, as a function. -/
def etaFn (x : G) : product p G :=
  ⟨fun _ ↦ QuotientGroup.mk x, fun _ _ _ ↦ rfl⟩

/-- The canonical quotient morphism to the maximal pro-`p` quotient. -/
def eta : G ⟶ product p G := ProfiniteGrp.ofHom {
  toFun := etaFn p G
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by
    apply continuous_induced_rng.mpr (continuous_pi _)
    intro U
    let q : G →* (diagram p G).obj U :=
      QuotientGroup.mk' U.toOpenNormalSubgroup.toSubgroup
    have hq : q.ker = U.toOpenNormalSubgroup.toSubgroup := by
      ext x
      exact QuotientGroup.eq_one_iff
        (N := U.toOpenNormalSubgroup.toSubgroup) x
    let _ : DiscreteTopology ((diagram p G).obj U) := ⟨rfl⟩
    change Continuous q
    apply continuous_of_continuousAt_one q
    rw [ContinuousAt, nhds_discrete ((diagram p G).obj U), map_one,
      tendsto_pure]
    change {x | q x = 1} ∈ nhds (1 : G)
    rw [show {x | q x = 1} = (q.ker : Set G) by ext x; simp, hq]
    exact U.toOpenNormalSubgroup.isOpen'.mem_nhds
      U.toOpenNormalSubgroup.toSubgroup.one_mem }

set_option backward.isDefEq.respectTransparency false in
omit [Fact p.Prime] in
/-- The canonical map to the maximal pro-`p` quotient has dense range. -/
theorem denseRange : DenseRange (etaFn p G) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsOpen, hs⟩ ⟨⟨spc, hspc⟩, hmem⟩
  rw [← hs, Set.mem_preimage] at hmem
  rcases (isOpen_pi_iff.mp hsOpen) _ hmem with ⟨J, fJ, hJ1, hJ2⟩
  let m : Quotient p G := J.inf id
  rcases QuotientGroup.mk'_surjective
      m.toOpenNormalSubgroup.toSubgroup (spc m) with ⟨origin, horigin⟩
  use etaFn p G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hs]
  apply hJ2
  intro a ha
  let mToA : m ⟶ a := (Finset.inf_le ha).hom
  rw [← (etaFn p G origin).property mToA]
  dsimp [etaFn] at ⊢ horigin
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc mToA) (hJ1 a ha).2

omit [Fact p.Prime] in
/-- The canonical map onto the maximal pro-`p` quotient is surjective. -/
theorem eta_surjective : Function.Surjective (eta p G) := by
  change Function.Surjective (etaFn p G)
  have hclosed : IsClosed (Set.range (etaFn p G)) :=
    isCompact_range (eta p G).hom.continuous_toFun |>.isClosed
  exact Set.range_eq_univ.mp <|
    hclosed.closure_eq.symm.trans (denseRange p G).closure_eq

omit [Fact p.Prime] in
/-- Every open normal subgroup of the maximal pro-`p` quotient pulls back
to contain one of the finite `p`-group quotient kernels. -/
theorem exists_quotient_le_comap
    (H : OpenNormalSubgroup (product p G)) :
    ∃ U : Quotient p G,
      U.toOpenNormalSubgroup.toSubgroup ≤
        H.toSubgroup.comap (eta p G).hom.toMonoidHom := by
  rcases H.isOpen' with ⟨s, hsOpen, hs⟩
  have hmem : (1 : product p G) ∈ Subtype.val ⁻¹' s := by
    rw [hs]
    exact H.toSubgroup.one_mem
  change (1 : product p G).val ∈ s at hmem
  rcases (isOpen_pi_iff.mp hsOpen) _ hmem with ⟨J, fJ, hJ1, hJ2⟩
  let m : Quotient p G := J.inf id
  refine ⟨m, ?_⟩
  intro x hx
  have hsMem : etaFn p G x ∈ Subtype.val ⁻¹' s := by
    change (etaFn p G x).val ∈ s
    apply hJ2
    intro a ha
    let mToA : m ⟶ a := (Finset.inf_le ha).hom
    have hm : (etaFn p G x).val m = 1 :=
      (QuotientGroup.eq_one_iff
        (N := m.toOpenNormalSubgroup.toSubgroup) x).mpr hx
    have haone : (etaFn p G x).val a = 1 := by
      rw [← (etaFn p G x).property mToA, hm, map_one]
    rw [haone]
    exact (hJ1 a ha).2
  rw [hs] at hsMem
  exact hsMem

omit [Fact p.Prime] in
/-- The finite quotient induced by an open normal subgroup of the maximal
pro-`p` quotient and a smaller defining `p`-group quotient kernel. -/
def openQuotientMap (H : OpenNormalSubgroup (product p G))
    (U : Quotient p G)
    (hU : U.toOpenNormalSubgroup.toSubgroup ≤
      H.toSubgroup.comap (eta p G).hom.toMonoidHom) :
    (G ⧸ U.toOpenNormalSubgroup.toSubgroup) →*
      (product p G ⧸ H.toSubgroup) :=
  QuotientGroup.map _ _ (eta p G).hom.toMonoidHom hU

omit [Fact p.Prime] in
/-- A finite quotient of the maximal pro-`p` quotient is reached from a
refining finite pro-`p` quotient of the original group. -/
theorem quotientMap_surjective (H : OpenNormalSubgroup (product p G))
    (U : Quotient p G)
    (hU : U.toOpenNormalSubgroup.toSubgroup ≤
      H.toSubgroup.comap (eta p G).hom.toMonoidHom) :
    Function.Surjective (openQuotientMap p G H U hU) := by
  intro z
  rcases QuotientGroup.mk'_surjective H.toSubgroup z with ⟨y, rfl⟩
  rcases eta_surjective p G y with ⟨x, rfl⟩
  exact ⟨QuotientGroup.mk x, rfl⟩

/-- The maximal pro-`p` quotient is a pro-`p` group. -/
instance product_isProP : IsProP p (product p G) where
  quotient_isPGroup H := by
    obtain ⟨U, hU⟩ := exists_quotient_le_comap p G H
    exact U.isPGroup'.of_surjective (openQuotientMap p G H U hU)
      (quotientMap_surjective p G H U hU)

variable {G}
variable {P : ProfiniteGrp.{u}} [IsProP p P]

/-- Pulling an open normal subgroup of a pro-`p` target back along a
continuous homomorphism gives a finite `p`-group quotient kernel. -/
def preimage (f : G →ₜ* P) (H : OpenNormalSubgroup P) :
    Quotient p G where
  toOpenNormalSubgroup :=
    { toSubgroup := H.toSubgroup.comap f.toMonoidHom
      isOpen' := H.isOpen'.preimage f.continuous_toFun }
  isPGroup' := by
    let q : G →* (P ⧸ H.toSubgroup) :=
      (QuotientGroup.mk' H.toSubgroup).comp f.toMonoidHom
    have htarget : IsPGroup p (P ⧸ H.toSubgroup) :=
      IsProP.quotient inferInstance H
    have hrange : IsPGroup p q.range := htarget.to_subgroup q.range
    have hker : q.ker = H.toSubgroup.comap f.toMonoidHom := by
      ext x
      exact QuotientGroup.eq_one_iff
        (N := H.toSubgroup) (f x)
    have hquot : IsPGroup p (G ⧸ q.ker) :=
      hrange.of_equiv (QuotientGroup.quotientKerEquivRange q).symm
    exact hquot.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)

/-- Refining a target quotient kernel refines its pullback kernel. This makes
the finite quotient maps compatible in the construction of `lift`. -/
theorem preimage_le {f : G →ₜ* P} {H K : OpenNormalSubgroup P}
    (h : H ≤ K) : preimage p f H ≤ preimage p f K :=
  Subgroup.comap_mono h

/-- The finite quotient map induced by a homomorphism to a pro-`p` target. -/
def quotientMap (f : G →ₜ* P) (H : OpenNormalSubgroup P) :
    FiniteGrp.of (G ⧸
      (preimage p f H).toOpenNormalSubgroup.toSubgroup) ⟶
      FiniteGrp.of (P ⧸ H.toSubgroup) :=
  FiniteGrp.ofHom <| QuotientGroup.map _ _ f.toMonoidHom fun _ h ↦ h

/-- Every continuous homomorphism from a profinite group to a pro-`p`
group factors through its maximal pro-`p` quotient. -/
noncomputable def lift (f : G →ₜ* P) : product p G ⟶ P :=
  P.isLimitCone.lift ⟨_, {
    app H := (limitCone (diagram p G)).π.app (preimage p f H) ≫
      (ofFiniteGrpHom <| quotientMap p f H)
    naturality := by
      intro X Y g
      ext ⟨x, hx⟩
      change quotientMap p f Y (x <| preimage p f Y) =
        P.diagram.map g (quotientMap p f X (x <| preimage p f X))
      have hxy := hx (preimage_le (p := p) (f := f) g.le).hom
      obtain ⟨t, ht⟩ : ∃ t : G,
          QuotientGroup.mk t = x (preimage p f X) :=
        QuotientGroup.mk_surjective (x (preimage p f X))
      rw [← hxy, ← ht]
      have hp := P.cone.π.naturality g
      apply_fun fun q ↦ q (f t) at hp
      exact hp
  }⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Precomposing the universal lift with the canonical quotient map recovers
the supplied continuous homomorphism, viewed as a profinite-group morphism. -/
@[reassoc (attr := simp)]
theorem lift_eta (f : G →ₜ* P) :
    eta p G ≫ lift p f = ProfiniteGrp.ofHom f := by
  let e := isoLimittoFiniteQuotientFunctor P
  rw [← e.cancel_iso_hom_right]
  rw [Category.assoc]
  change eta p G ≫ ((_ ≫ e.inv) ≫ e.hom) = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

omit [Fact p.Prime] [IsProP p P] in
/-- Morphisms out of the maximal pro-`p` quotient are determined by their
composites with the canonical quotient map. -/
theorem lift_unique (f g : product p G ⟶ P)
    (h : eta p G ≫ f = eta p G ≫ g) : f = g := by
  ext x
  obtain ⟨y, rfl⟩ := eta_surjective p G x
  simpa only [comp_apply] using ConcreteCategory.congr_hom h y

variable {Q : ProfiniteGrp.{u}} [IsProP p Q]

/-- The universal lift is natural in the pro-`p` target. -/
@[reassoc]
theorem lift_comp (f : G →ₜ* P) (g : P ⟶ Q) :
    lift p f ≫ g = lift p (g.hom.comp f) := by
  apply lift_unique
  simp only [lift_eta_assoc, lift_eta, ofHom_comp, ofHom_hom]

/-- Continuous homomorphisms from a profinite group to a pro-`p` group are
equivalent to morphisms from its maximal pro-`p` quotient. -/
noncomputable def homEquiv :
    (product p G ⟶ P) ≃ (G →ₜ* P) where
  toFun f := f.hom.comp (eta p G).hom
  invFun := lift p
  left_inv f := by
    apply lift_unique
    rw [lift_eta]
    ext x
    rfl
  right_inv f := by
    simpa only [hom_comp, hom_ofHom] using
      congrArg (fun k ↦ k.hom) (lift_eta (p := p) f)

/-- The forward universal-property correspondence precomposes a morphism
with the canonical quotient map and returns a continuous homomorphism. -/
@[simp]
theorem homEquiv_apply (f : product p G ⟶ P) :
    homEquiv (p := p) f = f.hom.comp (eta p G).hom := rfl

/-- The inverse universal-property correspondence is the factorization
`lift p` through the maximal pro-`p` quotient. -/
@[simp]
theorem homEquiv_symm_apply (f : G →ₜ* P) :
    (homEquiv (p := p)).symm f = lift p f := rfl

variable (G)

/-- The maximal pro-`p` quotient of a pro-`p` group is canonically isomorphic
to the group itself. -/
noncomputable def isoOfIsProP [IsProP p G] : product p G ≅ G where
  hom := lift p (ContinuousMonoidHom.id G)
  inv := eta p G
  hom_inv_id := by
    apply lift_unique
    simp only [lift_eta_assoc, ofHom_id, Category.comp_id,
      Category.id_comp]
  inv_hom_id := by
    simpa only [ofHom_id] using lift_eta p (ContinuousMonoidHom.id G)

/-- A morphism of profinite groups induces a morphism of their maximal
pro-`p` quotients. -/
noncomputable def map {G H : ProfiniteGrp.{u}} (f : G ⟶ H) :
    product p G ⟶ product p H :=
  lift p ((eta p H).hom.comp f.hom)

/-- The canonical quotient maps commute with the morphism induced by `f`.
This is the naturality equation for the maximal pro-`p` quotient. -/
@[reassoc (attr := simp)]
theorem eta_map {G H : ProfiniteGrp.{u}} (f : G ⟶ H) :
    eta p G ≫ map p f = f ≫ eta p H := by
  rw [map, lift_eta, ofHom_comp, ofHom_hom]
  change f ≫ eta p H = f ≫ eta p H
  rfl

/-- The identity morphism induces the identity on the maximal pro-`p`
quotient; this is the identity law used by `functor`. -/
@[simp]
theorem map_id (G : ProfiniteGrp.{u}) :
    map p (𝟙 G) = 𝟙 (product p G) := by
  apply lift_unique
  simp only [eta_map, Category.id_comp, Category.comp_id]

/-- The induced quotient morphisms respect composition, with `f` applied
before `g`; this is the composition law used by `functor`. -/
@[simp]
theorem map_comp {G H K : ProfiniteGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) :
    map p f ≫ map p g = map p (f ≫ g) := by
  apply lift_unique
  simp only [Category.assoc, eta_map, eta_map_assoc]

/-- Taking the maximal pro-`p` quotient is functorial. -/
noncomputable def functor :
    CategoryTheory.Functor ProfiniteGrp.{u} ProfiniteGrp.{u} where
  obj := product p
  map := map p
  map_id := map_id p
  map_comp := fun f g ↦ (map_comp p f g).symm

end MaximalProPQuotient

namespace FreeProPProduct

variable {ι : Type v} (p : ℕ) [Fact p.Prime]
variable (G : ι → ProfiniteGrp.{u})

/-- The free pro-`p` product of a family of profinite groups is the maximal
pro-`p` quotient of their free profinite product. -/
abbrev product : ProfiniteGrp.{max u v} :=
  MaximalProPQuotient.product p (FreeProduct.product G)

/-- The free pro-`p` product is pro-`p` even when no pro-`p` assumption is
made on the factors, since it is constructed as a maximal pro-`p` quotient. -/
instance product_isProP : IsProP p (product p G) := inferInstance

/-- The canonical continuous homomorphism from a factor to the free pro-`p`
product. -/
def of (i : ι) : G i →ₜ* product p G :=
  (MaximalProPQuotient.eta p (FreeProduct.product G)).hom.comp
    (FreeProduct.of G i)

variable {G}
variable {P : ProfiniteGrp.{max u v}} [IsProP p P]

/-- The morphism from the free pro-`p` product induced by a family of
continuous homomorphisms to a pro-`p` target. -/
noncomputable def lift (f : ∀ i, G i →ₜ* P) : product p G ⟶ P :=
  MaximalProPQuotient.lift p (FreeProduct.lift f).hom

/-- The free pro-`p` product's lift restricts to the requested map on each
factor, via the free profinite product and maximal pro-`p` quotient. -/
@[simp]
theorem lift_of (f : ∀ i, G i →ₜ* P) (i : ι) :
    (lift p f).hom.comp (of p G i) = f i := by
  ext x
  calc
    lift p f (of p G i x) =
        FreeProduct.lift f (FreeProduct.of G i x) := by
      exact ConcreteCategory.congr_hom
        (MaximalProPQuotient.lift_eta p (FreeProduct.lift f).hom)
        (FreeProduct.of G i x)
    _ = f i x := DFunLike.congr_fun (FreeProduct.lift_of f i) x

omit [Fact p.Prime] [IsProP p P] in
/-- Morphisms from the free pro-`p` product are determined by their
restrictions to the factors. -/
@[ext]
theorem hom_ext (f g : product p G ⟶ P)
    (h : ∀ i, f.hom.comp (of p G i) = g.hom.comp (of p G i)) : f = g := by
  apply MaximalProPQuotient.lift_unique
  apply FreeProduct.hom_ext
  intro i
  ext x
  simpa only [hom_comp, ContinuousMonoidHom.comp_toFun, of] using
    DFunLike.congr_fun (h i) x

variable {Q : ProfiniteGrp.{max u v}} [IsProP p Q]

/-- The universal lift is natural in the pro-`p` target. -/
@[reassoc]
theorem lift_comp (f : ∀ i, G i →ₜ* P) (g : P ⟶ Q) :
    lift p f ≫ g = lift p fun i ↦ g.hom.comp (f i) := by
  apply hom_ext
  intro i
  change g.hom.comp ((lift p f).hom.comp (of p G i)) =
    (lift p fun i ↦ g.hom.comp (f i)).hom.comp (of p G i)
  rw [lift_of, lift_of]

/-- Continuous homomorphisms from the free pro-`p` product to a pro-`p` group
are equivalent to families of continuous homomorphisms from its factors. -/
noncomputable def homEquiv :
    (product p G ⟶ P) ≃ (∀ i, G i →ₜ* P) where
  toFun f i := f.hom.comp (of p G i)
  invFun := lift p
  left_inv f := by
    apply hom_ext
    intro i
    exact lift_of p (fun j ↦ f.hom.comp (of p G j)) i
  right_inv f := funext fun i ↦ lift_of p f i

/-- The forward universal-property correspondence restricts a morphism from
the free pro-`p` product to the indicated factor. -/
@[simp]
theorem homEquiv_apply (f : product p G ⟶ P) (i : ι) :
    homEquiv (p := p) f i = f.hom.comp (of p G i) := rfl

/-- The inverse universal-property correspondence extends the family by
`lift p`, with the pro-`p` assumption on its target. -/
@[simp]
theorem homEquiv_symm_apply (f : ∀ i, G i →ₜ* P) :
    (homEquiv (p := p)).symm f = lift p f := rfl

variable (G)

/-- A factor lifted to the universe of its free pro-`p` product. -/
private def liftedFactor (i : ι) : ProfiniteGrp.{max u v} :=
  ProfiniteGrp.ofContinuousMulEquiv (G := G i) (H := ULift.{v} (G i))
    { toFun := ULift.up
      invFun := ULift.down
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_uliftUp
      continuous_invFun := continuous_uliftDown }

private def factorEquiv (i : ι) : G i ≃ₜ* liftedFactor G i where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_uliftUp
  continuous_invFun := continuous_uliftDown

private instance liftedFactor_isProP [∀ i, IsProP p (G i)] (i : ι) :
    IsProP p (liftedFactor G i) :=
  IsProP.of_continuousMulEquiv (inferInstance : IsProP p (G i))
    (factorEquiv G i)

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

private noncomputable def factorRetraction [∀ i, IsProP p (G i)] (i : ι) :
    product p G ⟶ liftedFactor G i := by
  classical
  exact lift p (Function.update (trivialToFactor G i) i (factorUp G i))

@[simp]
private theorem factorRetraction_of [∀ i, IsProP p (G i)] (i : ι) :
    (factorRetraction p G i).hom.comp (of p G i) = factorUp G i := by
  classical
  rw [factorRetraction, lift_of]
  exact Function.update_self i (factorUp G i) (trivialToFactor G i)

/-- If every factor is pro-`p`, each canonical factor map into the free
pro-`p` product is injective. -/
theorem of_injective [∀ i, IsProP p (G i)] (i : ι) :
    Function.Injective (of p G i) := by
  intro x y hxy
  have hleft := DFunLike.congr_fun (factorRetraction_of p G i) x
  have hright := DFunLike.congr_fun (factorRetraction_of p G i) y
  have h : factorUp G i x = factorUp G i y := by
    rw [← hleft, ← hright]
    exact congrArg (factorRetraction p G i) hxy
  exact congrArg ULift.down h

variable {H K : ι → ProfiniteGrp.{u}}

/-- A family of continuous homomorphisms induces a morphism of free pro-`p`
products. -/
noncomputable def map (f : ∀ i, G i →ₜ* H i) :
    product p G ⟶ product p H :=
  lift p fun i ↦ (of p H i).comp (f i)

/-- The morphism induced by a family of continuous homomorphisms commutes
with each canonical factor map, whether or not the factors are pro-`p`. -/
@[simp]
theorem map_of (f : ∀ i, G i →ₜ* H i) (i : ι) :
    (map p G f).hom.comp (of p G i) = (of p H i).comp (f i) :=
  lift_of p _ i

/-- Identity maps on all factors induce the identity of their free pro-`p`
product. -/
@[simp]
theorem map_id :
    map p G (fun i ↦ ContinuousMonoidHom.id (G i)) = 𝟙 (product p G) := by
  apply hom_ext
  intro i
  rw [map_of]
  rfl

/-- Mapping free pro-`p` products twice agrees with mapping the componentwise
composites of the factor homomorphisms. -/
@[simp]
theorem map_comp (f : ∀ i, G i →ₜ* H i) (g : ∀ i, H i →ₜ* K i) :
    map p G f ≫ map p H g = map p G fun i ↦ (g i).comp (f i) := by
  apply hom_ext
  intro i
  ext x
  change (map p H g).hom ((map p G f).hom (of p G i x)) =
    (map p G fun i ↦ (g i).comp (f i)).hom (of p G i x)
  rw [show (map p G f).hom (of p G i x) = of p H i (f i x) by
    exact DFunLike.congr_fun (map_of p G f i) x]
  rw [show (map p H g).hom (of p H i (f i x)) = of p K i (g i (f i x)) by
    exact DFunLike.congr_fun (map_of p H g i) (f i x)]
  rw [show (map p G fun i ↦ (g i).comp (f i)).hom (of p G i x) =
      of p K i (g i (f i x)) by
    exact DFunLike.congr_fun (map_of p G (fun i ↦ (g i).comp (f i)) i) x]

end FreeProPProduct

end ProfiniteGrp
