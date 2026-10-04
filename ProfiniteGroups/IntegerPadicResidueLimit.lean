/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicResidueLimit
public import ProfiniteGroups.PrimewisePadic

/-!
# Residue limits of the p-adic integers and completed integers

Powers of a fixed prime reindex the existing supported-residue diagram by
reverse natural order. Its finite stages are additive `ZMod (p ^ k)`, written
multiplicatively and lifted to the ambient universe; its arrows are reductions
at smaller exponents. At exponent zero the stage is `ZMod 1`.

The p-adic factor and the completed integers have canonical continuous group
comparisons with the p-power residue limit and the all-positive residue limit,
respectively. Coordinate equations normalize the former by p-adic reduction
and the latter by reduction of integral casts. The completed-integer diagram
uses strictly positive moduli, including one, with no zero-modulus stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ProfiniteGrp

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The level `p ^ k` in the positive indices supported at `p`. -/
def pPowerIndexLevel (p : Nat.Primes) (k : ℕ) : Nat.PowerIndex {p} :=
  Nat.PowerIndex.ofSupported (p.1 ^ k)
    ((Nat.primeSupportedIndices {p}).pow_mem
      ((Nat.prime_mem_primeSupportedIndices_iff p).mpr (Set.mem_singleton p)) k)

/-- The exponent of the indexed p-power stage is exactly `p ^ k`. -/
@[simp] theorem pPowerIndexLevel_val (p : Nat.Primes) (k : ℕ) :
    (pPowerIndexLevel p k).val = p.1 ^ k := rfl

/-- Exponent zero is the terminal, modulus-one stage. -/
@[simp] theorem pPowerIndexLevel_zero (p : Nat.Primes) :
    pPowerIndexLevel p 0 = ⊤ := by
  apply Nat.PowerIndex.ext
  simp

/-- Reverse natural order maps to reverse divisibility of positive p-powers. -/
def pPowerIndex (p : Nat.Primes) : ℕᵒᵈ ⥤ Nat.PowerIndex {p} :=
  (show Monotone (fun k : ℕᵒᵈ ↦ pPowerIndexLevel p (OrderDual.ofDual k)) from
    fun _ _ h ↦ (Nat.PowerIndex.le_iff _ _).mpr
      (pow_dvd_pow p.1 (show OrderDual.ofDual _ ≤ OrderDual.ofDual _ from h))).functor

/-- The indexing functor selects the indicated p-power level. -/
@[simp] theorem pPowerIndex_obj (p : Nat.Primes) (k : ℕᵒᵈ) :
    (pPowerIndex p).obj k = pPowerIndexLevel p (OrderDual.ofDual k) := rfl

/-- The selected arrow witnesses divisibility of the corresponding p-powers. -/
@[simp] theorem pPowerIndex_map (p : Nat.Primes) {k j : ℕᵒᵈ} (f : k ⟶ j) :
    (pPowerIndex p).map f =
      homOfLE ((Nat.PowerIndex.le_iff _ _).mpr
        (pow_dvd_pow p.1 (show OrderDual.ofDual j ≤ OrderDual.ofDual k from f.le))) :=
  Subsingleton.elim _ _

/-- The finite p-power system is the existing supported-residue system
precomposed with p-power indexing. -/
def pPowerResidueFiniteFunctor (p : Nat.Primes) : ℕᵒᵈ ⥤ FiniteGrp.{u} :=
  pPowerIndex p ⋙ residueFiniteFunctor.{u} {p}

/-- The profinite p-power system is the existing supported-residue system
precomposed with p-power indexing. -/
def pPowerResidueDiagram (p : Nat.Primes) : ℕᵒᵈ ⥤ ProfiniteGrp.{u} :=
  pPowerIndex p ⋙ residueDiagram.{u} {p}

/-- The `k`-th p-power stage is the finite additive group `ZMod (p ^ k)`. -/
@[simp] theorem pPowerResidueDiagram_obj (p : Nat.Primes) (k : ℕᵒᵈ) :
    ((pPowerResidueDiagram.{u} p).obj k : Type u) =
      ULift.{u} (Multiplicative (ZMod (p.1 ^ OrderDual.ofDual k))) := rfl

/-- Finite and profinite p-power diagrams have the same discrete stages. -/
@[simp] theorem pPowerResidueFiniteFunctor_obj (p : Nat.Primes) (k : ℕᵒᵈ) :
    ((pPowerResidueFiniteFunctor.{u} p).obj k : Type u) =
      ULift.{u} (Multiplicative (ZMod (p.1 ^ OrderDual.ofDual k))) := rfl

/-- Every profinite p-power arrow reduces the residue at its larger exponent. -/
@[simp] theorem pPowerResidueDiagram_map_apply (p : Nat.Primes)
    {k j : ℕᵒᵈ} (f : k ⟶ j) (a : ZMod (p.1 ^ OrderDual.ofDual k)) :
    (pPowerResidueDiagram.{u} p).map f
        (ULift.up (Multiplicative.ofAdd a)) =
      ULift.up (Multiplicative.ofAdd
        (ZMod.castHom (pow_dvd_pow p.1
          (show OrderDual.ofDual j ≤ OrderDual.ofDual k from f.le))
          (ZMod (p.1 ^ OrderDual.ofDual j)) a)) :=
  residueDiagram_map_apply.{u} {p} ((pPowerIndex p).map f) a

/-- Every finite p-power arrow has the same residue-reduction formula. -/
@[simp] theorem pPowerResidueFiniteFunctor_map_apply (p : Nat.Primes)
    {k j : ℕᵒᵈ} (f : k ⟶ j) (a : ZMod (p.1 ^ OrderDual.ofDual k)) :
    (pPowerResidueFiniteFunctor.{u} p).map f
        (ULift.up (Multiplicative.ofAdd a)) =
      ULift.up (Multiplicative.ofAdd
        (ZMod.castHom (pow_dvd_pow p.1
          (show OrderDual.ofDual j ≤ OrderDual.ofDual k from f.le))
          (ZMod (p.1 ^ OrderDual.ofDual j)) a)) :=
  residueFiniteFunctor_map_apply.{u} {p} ((pPowerIndex p).map f) a

/-- The universal lift of a continuous compatible cone evaluates to its
given coordinate at every p-power level. Uniqueness is the `uniq` field of
`ProfiniteGrp.limitConeIsLimit`. -/
@[simp] theorem pPowerResidueLimit_lift_apply (p : Nat.Primes)
    (c : Cone (pPowerResidueDiagram.{u} p)) (k : ℕᵒᵈ) (x : c.pt) :
    (((ProfiniteGrp.limitConeIsLimit (pPowerResidueDiagram p)).lift c) x).val k =
      c.π.app k x := by
  have h := congrArg (fun f : c.pt ⟶ (pPowerResidueDiagram p).obj k ↦ f x)
    ((ProfiniteGrp.limitConeIsLimit (pPowerResidueDiagram p)).fac c k)
  change ((ProfiniteGrp.limitCone (pPowerResidueDiagram p)).π.app k)
    (((ProfiniteGrp.limitConeIsLimit (pPowerResidueDiagram p)).lift c) x) =
      c.π.app k x at h
  exact h

/-- The universal lift at all positive moduli has the prescribed residue
coordinate; its uniqueness is already supplied by `limitConeIsLimit`. -/
@[simp] theorem integerResidueLimit_lift_apply
    (c : Cone (residueDiagram.{u} (Set.univ : Set Nat.Primes)))
    (n : Nat.PowerIndex (Set.univ : Set Nat.Primes)) (x : c.pt) :
    (((ProfiniteGrp.limitConeIsLimit
      (residueDiagram (Set.univ : Set Nat.Primes))).lift c) x).val n =
      c.π.app n x := by
  have h := congrArg (fun f : c.pt ⟶ (residueDiagram _).obj n ↦ f x)
    ((ProfiniteGrp.limitConeIsLimit (residueDiagram _)).fac c n)
  change ((ProfiniteGrp.limitCone (residueDiagram _)).π.app n)
    (((ProfiniteGrp.limitConeIsLimit (residueDiagram _)).lift c) x) =
      c.π.app n x at h
  exact h

private theorem surjective_limit_lift_of_surjective
    {J : Type v} [PartialOrder J] [IsCodirectedOrder J] [Nonempty J]
    (F : J ⥤ ProfiniteGrp.{max u v}) (c : Cone F)
    (h : ∀ j, Function.Surjective (c.π.app j)) :
    Function.Surjective ((ProfiniteGrp.limitConeIsLimit F).lift c) := by
  intro y
  let fiber (j : J) : Set c.pt := {x | c.π.app j x = y.val j}
  have hclosed (j : J) : IsClosed (fiber j) :=
    isClosed_singleton.preimage (c.π.app j).hom.continuous_toFun
  have hnonempty (j : J) : (fiber j).Nonempty := by
    obtain ⟨x, hx⟩ := h j (y.val j)
    exact ⟨x, hx⟩
  have hmono {i j : J} (hij : i ≤ j) : fiber i ⊆ fiber j := by
    intro x hx
    have hc := congrArg (fun f : c.pt ⟶ F.obj j ↦ f x) (c.w (homOfLE hij))
    change F.map (homOfLE hij) (c.π.app i x) = c.π.app j x at hc
    change c.π.app j x = y.val j
    have hy : F.map (homOfLE hij) (y.val i) = y.val j := y.2 (homOfLE hij)
    exact hc.symm.trans ((congrArg
      (fun z : F.obj i ↦ F.map (homOfLE hij) z) hx).trans hy)
  have hdirected : Directed (· ⊇ ·) fiber := by
    intro i j
    obtain ⟨k, hki, hkj⟩ := exists_le_le i j
    exact ⟨k, hmono hki, hmono hkj⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    fiber hdirected hnonempty (fun j ↦ (hclosed j).isCompact) hclosed
  refine ⟨x, ?_⟩
  apply ProfiniteGrp.limit_ext
  intro j
  have hc := congrArg (fun f : c.pt ⟶ F.obj j ↦ f x)
    ((ProfiniteGrp.limitConeIsLimit F).fac c j)
  change (((ProfiniteGrp.limitConeIsLimit F).lift c x).val j) = c.π.app j x at hc
  exact hc.trans (Set.mem_iInter.mp hx j)

/-- The integral unit in the multiplicative p-adic factor. -/
noncomputable def padicFactorGenerator (p : Nat.Primes) : padicFactor.{u} p :=
  Multiplicative.ofAdd (ULift.up (1 : ℤ_[p.1]))

/-- The integral unit topologically generates the p-adic factor. -/
theorem padicFactorGenerator_isTopologicalGenerator (p : Nat.Primes) :
    IsTopologicalGenerator (padicFactor.{u} p) (padicFactorGenerator p) := by
  have hdense : DenseRange (fun z : ℤ ↦
      Multiplicative.ofAdd (ULift.up (z : ℤ_[p.1])) : ℤ → padicFactor.{u} p) := by
    have hsurj : Function.Surjective
        (fun z : ℤ_[p.1] ↦ Multiplicative.ofAdd (ULift.up z) :
          ℤ_[p.1] → padicFactor.{u} p) := by
      intro x
      exact ⟨x.toAdd.down, rfl⟩
    exact (hsurj.denseRange.comp PadicInt.denseRange_intCast
      (continuous_ofAdd.comp continuous_uliftUp))
  rw [IsTopologicalGenerator,
    show (fun z : ℤ ↦ padicFactorGenerator.{u} p ^ z) =
      (fun z : ℤ ↦ Multiplicative.ofAdd (ULift.up (z : ℤ_[p.1]))) by
        funext z
        apply Multiplicative.toAdd.injective
        change z • (ULift.up (1 : ℤ_[p.1])) = ULift.up (z : ℤ_[p.1])
        apply ULift.down_injective
        simp]
  exact hdense

/-- Every p-adic factor is procyclic, with its integral unit as witness. -/
theorem padicFactor_isProcyclic (p : Nat.Primes) :
    IsProcyclic (padicFactor.{u} p) :=
  ⟨padicFactorGenerator p, padicFactorGenerator_isTopologicalGenerator p⟩

/-- The completed integers' distinguished integral unit. -/
def integerCompletionGenerator : integerCompletion.{u} :=
  ProfiniteCompletion.etaFn (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
    (ULift.up (Multiplicative.ofAdd (1 : ℤ)))

/-- The residue at a positive index, forgetting only the existing
multiplicative and universe-lift wrappers. -/
noncomputable def integerCompletionResidueAt
    (n : Nat.PowerIndex (Set.univ : Set Nat.Primes))
    (x : integerCompletion.{u}) : ZMod n.val := by
  letI : NeZero n.val := ⟨n.pos.ne'⟩
  exact (integerCompletionResidue n.val x).toAdd.down

/-- At an integral cast, the coordinate is the usual modular cast. -/
@[simp] theorem integerCompletionResidueAt_eta_int
    (n : Nat.PowerIndex (Set.univ : Set Nat.Primes)) (z : ℤ) :
    integerCompletionResidueAt.{u} n
        (ProfiniteCompletion.etaFn (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
          (ULift.up (Multiplicative.ofAdd z))) = (z : ZMod n.val) := by
  let _ : NeZero n.val := ⟨n.pos.ne'⟩
  change (integerCompletionResidue.{u} n.val
    (ProfiniteCompletion.etaFn _ (ULift.up (Multiplicative.ofAdd z)))).toAdd.down = _
  rw [integerCompletionResidue_eta]
  rfl

/-- Reducing a completed-integer coordinate along a positive-index arrow gives
the coordinate at its target. -/
theorem integerCompletionResidueAt_cast
    {n d : Nat.PowerIndex (Set.univ : Set Nat.Primes)} (f : n ⟶ d)
    (x : integerCompletion.{u}) :
    ZMod.cast (integerCompletionResidueAt n x) =
      integerCompletionResidueAt d x := by
  let _ : NeZero n.val := ⟨n.pos.ne'⟩
  let _ : NeZero d.val := ⟨d.pos.ne'⟩
  change ZMod.cast (integerCompletionResidue.{u} n.val x).toAdd.down =
    (integerCompletionResidue.{u} d.val x).toAdd.down
  exact integerCompletionResidue_cast (Nat.PowerIndex.dvd_of_hom f) x

/-- The completed-integer coordinates form a compatible family for the
all-positive residue diagram. -/
theorem integerCompletionResidueAt_map
    {n d : Nat.PowerIndex (Set.univ : Set Nat.Primes)} (f : n ⟶ d)
    (x : integerCompletion.{u}) :
    (residueDiagram.{u} (Set.univ : Set Nat.Primes)).map f
        (ULift.up (Multiplicative.ofAdd (integerCompletionResidueAt n x))) =
      ULift.up (Multiplicative.ofAdd (integerCompletionResidueAt d x)) := by
  rw [residueDiagram_map_apply]
  exact congrArg (fun a : ZMod d.val ↦ ULift.up (Multiplicative.ofAdd a))
    (integerCompletionResidueAt_cast f x)

/-- Equality of every positive-index coordinate implies equality of completed integers. -/
theorem integerCompletionResidueAt_ext {x y : integerCompletion.{u}}
    (h : ∀ n : Nat.PowerIndex (Set.univ : Set Nat.Primes),
      integerCompletionResidueAt n x = integerCompletionResidueAt n y) :
    x = y := by
  apply integerCompletionResidue_jointly_injective
  intro n _
  let index := Nat.PowerIndex.ofPositive n (Nat.pos_of_ne_zero (NeZero.ne n))
  apply Multiplicative.toAdd.injective
  apply ULift.down_injective
  exact h index

private noncomputable def padicResidueCone (p : Nat.Primes) :
    Cone (pPowerResidueDiagram.{u} p) where
  pt := padicFactor p
  π := {
    app k := by
      apply ConcreteCategory.ofHom
      exact {
        toFun := fun x ↦ ULift.up (Multiplicative.ofAdd
          (PadicInt.toZModPow (OrderDual.ofDual k) x.toAdd.down))
        map_one' := by
          change ULift.up (Multiplicative.ofAdd
            (PadicInt.toZModPow (OrderDual.ofDual k) (0 : ℤ_[p.1]))) = _
          rw [map_zero]
          rfl
        map_mul' := by
          intro x y
          change ULift.up (Multiplicative.ofAdd
            (PadicInt.toZModPow (OrderDual.ofDual k) (x.toAdd.down + y.toAdd.down))) = _
          rw [map_add]
          rfl
        continuous_toFun := by
          have htop : (inferInstance : TopologicalSpace (ULift.{u}
              (Multiplicative (ZMod (p.1 ^ OrderDual.ofDual k))))) =
              ((pPowerResidueDiagram.{u} p).obj k).toProfinite.toTop.str := by
            rw [DiscreteTopology.eq_bot (α := ULift.{u}
              (Multiplicative (ZMod (p.1 ^ OrderDual.ofDual k))))]
            rfl
          change @Continuous _ _ _ ((pPowerResidueDiagram.{u} p).obj k).toProfinite.toTop.str _
          rw [← htop]
          exact (continuous_uliftUp.comp continuous_ofAdd).comp
            ((continuous_toZModPow p (OrderDual.ofDual k)).comp
              (continuous_uliftDown.comp continuous_toAdd)) }
    naturality := by
      intro i j f
      ext x
      change ULift.up (Multiplicative.ofAdd
        (PadicInt.toZModPow (OrderDual.ofDual j) x.toAdd.down)) =
        (pPowerResidueDiagram.{u} p).map f
          (ULift.up (Multiplicative.ofAdd
            (PadicInt.toZModPow (OrderDual.ofDual i) x.toAdd.down)))
      rw [pPowerResidueDiagram_map_apply]
      exact congrArg (fun a : ZMod (p.1 ^ OrderDual.ofDual j) ↦
        ULift.up (Multiplicative.ofAdd a))
        (PadicInt.cast_toZModPow (OrderDual.ofDual j) (OrderDual.ofDual i) f.le
          x.toAdd.down).symm }

private noncomputable def integerResidueCone :
    Cone (residueDiagram.{u} (Set.univ : Set Nat.Primes)) where
  pt := integerCompletion
  π := {
    app n := by
      let _ : NeZero n.val := ⟨n.pos.ne'⟩
      apply ConcreteCategory.ofHom
      exact {
        toFun := fun x ↦ ULift.up (Multiplicative.ofAdd
          (integerCompletionResidueAt n x))
        map_one' := by
          exact congrArg
            (fun a : Multiplicative (ULift.{u} (ZMod n.val)) ↦
              ULift.up (Multiplicative.ofAdd a.toAdd.down))
            (map_one (integerCompletionResidueHom.{u} n.val).hom)
        map_mul' := by
          intro x y
          exact congrArg
            (fun a : Multiplicative (ULift.{u} (ZMod n.val)) ↦
              ULift.up (Multiplicative.ofAdd a.toAdd.down))
            (map_mul (integerCompletionResidueHom.{u} n.val).hom x y)
        continuous_toFun := by
          have htop : (inferInstance : TopologicalSpace
              (ULift.{u} (Multiplicative (ZMod n.val)))) =
              ((residueDiagram.{u} (Set.univ : Set Nat.Primes)).obj n).toProfinite.toTop.str := by
            rw [DiscreteTopology.eq_bot (α := ULift.{u} (Multiplicative (ZMod n.val)))]
            rfl
          change @Continuous _ _ _
            ((residueDiagram.{u} (Set.univ : Set Nat.Primes)).obj n).toProfinite.toTop.str _
          rw [← htop]
          exact (continuous_uliftUp.comp continuous_ofAdd).comp
            ((continuous_uliftDown.comp continuous_toAdd).comp
              (continuous_integerCompletionResidue.{u} n.val)) }
    naturality := by
      intro n d f
      ext x
      exact (integerCompletionResidueAt_map f x).symm }

/-- A p-adic factor has a continuous multiplicative comparison with its
p-power residue limit whose coordinates are the canonical reductions. -/
theorem exists_padicFactorEquivPowerResidueLimit (p : Nat.Primes) :
    ∃ e : padicFactor.{u} p ≃ₜ* ProfiniteGrp.limit (pPowerResidueDiagram.{u} p),
      ∀ (k : ℕᵒᵈ) (x : padicFactor.{u} p),
        (e x).val k = ULift.up (Multiplicative.ofAdd
          (PadicInt.toZModPow (OrderDual.ofDual k) x.toAdd.down)) := by
  let c := padicResidueCone.{u} p
  let f := (ProfiniteGrp.limitConeIsLimit (pPowerResidueDiagram.{u} p)).lift c
  have hstage (k : ℕᵒᵈ) : Function.Surjective (c.π.app k) := by
    rintro ⟨a⟩
    obtain ⟨x, hx⟩ := liftedPadicToZModPow_surjective.{u} p
      (OrderDual.ofDual k) a.toAdd
    refine ⟨Multiplicative.ofAdd x, ?_⟩
    change ULift.up (Multiplicative.ofAdd
      (liftedPadicToZModPow p (OrderDual.ofDual k) x)) = ULift.up a
    rw [hx]
    rfl
  have hsurj : Function.Surjective f :=
    surjective_limit_lift_of_surjective _ c hstage
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Multiplicative.toAdd.injective
    apply ULift.down_injective
    apply (PadicInt.ext_of_toZModPow).mp
    intro k
    have h := congrArg (fun z : ProfiniteGrp.limit (pPowerResidueDiagram.{u} p) ↦
      z.val (OrderDual.toDual k)) hxy
    change ULift.up (Multiplicative.ofAdd (PadicInt.toZModPow k x.toAdd.down)) =
      ULift.up (Multiplicative.ofAdd (PadicInt.toZModPow k y.toAdd.down)) at h
    exact congrArg (fun a : ULift.{u} (Multiplicative (ZMod (p.1 ^ k))) ↦
      a.down.toAdd) h
  refine ⟨ContinuousMulEquiv.mk'
    ((isHomeomorph_iff_continuous_bijective.mpr
      ⟨f.hom.continuous_toFun, hinj, hsurj⟩).homeomorph (fun x ↦ f x))
    f.hom.map_mul, ?_⟩
  intro k x
  exact pPowerResidueLimit_lift_apply p c k x

/-- The canonical, coordinate-normalized topological group equivalence from
a p-adic factor to its p-power residue limit. -/
noncomputable def padicFactorEquivPowerResidueLimit (p : Nat.Primes) :
    padicFactor.{u} p ≃ₜ* ProfiniteGrp.limit (pPowerResidueDiagram.{u} p) :=
  Classical.choose (exists_padicFactorEquivPowerResidueLimit p)

/-- Evaluating the p-adic comparison at any power is `toZModPow`. -/
@[simp] theorem padicFactorEquivPowerResidueLimit_apply
    (p : Nat.Primes) (k : ℕᵒᵈ) (x : padicFactor.{u} p) :
    (padicFactorEquivPowerResidueLimit p x).val k =
      ULift.up (Multiplicative.ofAdd
        (PadicInt.toZModPow (OrderDual.ofDual k) x.toAdd.down)) :=
  (Classical.choose_spec (exists_padicFactorEquivPowerResidueLimit p)) k x

/-- The p-adic reduction coordinates uniquely determine the continuous
comparison, independently of the chosen existence witness. -/
theorem padicFactorEquivPowerResidueLimit_unique (p : Nat.Primes)
    (e : padicFactor.{u} p ≃ₜ* ProfiniteGrp.limit (pPowerResidueDiagram.{u} p))
    (he : ∀ (k : ℕᵒᵈ) (x : padicFactor.{u} p),
      (e x).val k = ULift.up (Multiplicative.ofAdd
        (PadicInt.toZModPow (OrderDual.ofDual k) x.toAdd.down))) :
    e = padicFactorEquivPowerResidueLimit p := by
  apply ContinuousMulEquiv.ext
  intro x
  apply ProfiniteGrp.limit_ext
  intro k
  exact (he k x).trans (padicFactorEquivPowerResidueLimit_apply p k x).symm

/-- The canonical generator has residue one in every p-power coordinate. -/
@[simp] theorem padicFactorEquivPowerResidueLimit_generator
    (p : Nat.Primes) (k : ℕᵒᵈ) :
    (padicFactorEquivPowerResidueLimit.{u} p (padicFactorGenerator p)).val k =
      ULift.up (Multiplicative.ofAdd (1 : ZMod (p.1 ^ OrderDual.ofDual k))) := by
  rw [padicFactorEquivPowerResidueLimit_apply]
  exact congrArg (fun a : ZMod (p.1 ^ OrderDual.ofDual k) ↦
    ULift.up (Multiplicative.ofAdd a)) (map_one (PadicInt.toZModPow _))

/-- The all-positive residue limit is canonically equivalent to the
completed integers, with the already-defined completion residues as coordinates. -/
theorem exists_integerCompletionEquivResidueLimit :
    ∃ e : integerCompletion.{u} ≃ₜ*
        ProfiniteGrp.limit (residueDiagram.{u} (Set.univ : Set Nat.Primes)),
      ∀ (n : Nat.PowerIndex (Set.univ : Set Nat.Primes))
        (x : integerCompletion.{u}),
        (e x).val n = ULift.up (Multiplicative.ofAdd
          (integerCompletionResidueAt n x)) := by
  let c := integerResidueCone.{u}
  let f := (ProfiniteGrp.limitConeIsLimit
    (residueDiagram.{u} (Set.univ : Set Nat.Primes))).lift c
  have hstage (n : Nat.PowerIndex (Set.univ : Set Nat.Primes)) :
      Function.Surjective (c.π.app n) := by
    rintro ⟨a⟩
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective a.toAdd
    refine ⟨ProfiniteCompletion.etaFn (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
      (ULift.up (Multiplicative.ofAdd z)), ?_⟩
    change ULift.up (Multiplicative.ofAdd
      (integerCompletionResidueAt n
        (ProfiniteCompletion.etaFn _ (ULift.up (Multiplicative.ofAdd z))))) =
      ULift.up a
    rw [integerCompletionResidueAt_eta_int, hz]
    rfl
  have hsurj : Function.Surjective f :=
    surjective_limit_lift_of_surjective _ c hstage
  have hinj : Function.Injective f := by
    intro x y hxy
    apply integerCompletionResidueAt_ext
    intro n
    have h := congrArg (fun z : ProfiniteGrp.limit
      (residueDiagram.{u} (Set.univ : Set Nat.Primes)) ↦ z.val n) hxy
    change ULift.up (Multiplicative.ofAdd (integerCompletionResidueAt n x)) =
      ULift.up (Multiplicative.ofAdd (integerCompletionResidueAt n y)) at h
    exact congrArg (fun a : ULift.{u} (Multiplicative (ZMod n.val)) ↦ a.down.toAdd) h
  refine ⟨ContinuousMulEquiv.mk'
    ((isHomeomorph_iff_continuous_bijective.mpr
      ⟨f.hom.continuous_toFun, hinj, hsurj⟩).homeomorph (fun x ↦ f x))
    f.hom.map_mul, ?_⟩
  intro n x
  exact integerResidueLimit_lift_apply c n x

/-- The canonical, coordinate-normalized topological group equivalence from
the completed integers to the all-positive residue limit. -/
noncomputable def integerCompletionEquivResidueLimit :
    integerCompletion.{u} ≃ₜ*
      ProfiniteGrp.limit (residueDiagram.{u} (Set.univ : Set Nat.Primes)) :=
  Classical.choose exists_integerCompletionEquivResidueLimit

/-- Every coordinate of the completed-integer comparison is the existing
completion residue map. -/
@[simp] theorem integerCompletionEquivResidueLimit_apply
    (n : Nat.PowerIndex (Set.univ : Set Nat.Primes))
    (x : integerCompletion.{u}) :
    (integerCompletionEquivResidueLimit x).val n =
      ULift.up (Multiplicative.ofAdd (integerCompletionResidueAt n x)) :=
  (Classical.choose_spec exists_integerCompletionEquivResidueLimit) n x

/-- The existing completion residues uniquely determine this comparison. -/
theorem integerCompletionEquivResidueLimit_unique
    (e : integerCompletion.{u} ≃ₜ*
      ProfiniteGrp.limit (residueDiagram.{u} (Set.univ : Set Nat.Primes)))
    (he : ∀ (n : Nat.PowerIndex (Set.univ : Set Nat.Primes))
      (x : integerCompletion.{u}),
      (e x).val n = ULift.up (Multiplicative.ofAdd
        (integerCompletionResidueAt n x))) :
    e = integerCompletionEquivResidueLimit := by
  apply ContinuousMulEquiv.ext
  intro x
  apply ProfiniteGrp.limit_ext
  intro n
  exact (he n x).trans (integerCompletionEquivResidueLimit_apply n x).symm

/-- Integral casts have their ordinary residues at every positive modulus. -/
@[simp] theorem integerCompletionEquivResidueLimit_eta_int
    (n : Nat.PowerIndex (Set.univ : Set Nat.Primes)) (z : ℤ) :
    (integerCompletionEquivResidueLimit.{u}
        (ProfiniteCompletion.etaFn (GrpCat.of (ULift.{u} (Multiplicative ℤ)))
          (ULift.up (Multiplicative.ofAdd z)))).val n =
      ULift.up (Multiplicative.ofAdd (z : ZMod n.val)) := by
  rw [integerCompletionEquivResidueLimit_apply,
    integerCompletionResidueAt_eta_int]

/-- The completed-integer generator maps to residue one at every level. -/
@[simp] theorem integerCompletionEquivResidueLimit_generator
    (n : Nat.PowerIndex (Set.univ : Set Nat.Primes)) :
    (integerCompletionEquivResidueLimit.{u} integerCompletionGenerator).val n =
      ULift.up (Multiplicative.ofAdd (1 : ZMod n.val)) := by
  simpa only [integerCompletionGenerator, Int.cast_one] using
    integerCompletionEquivResidueLimit_eta_int n 1

end ProfiniteGrp
