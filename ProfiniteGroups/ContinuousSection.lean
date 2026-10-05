/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Separation.DisjointCover
public import GroupTheory.Topology.OpenQuotient
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Order.Zorn
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Continuous sections of profinite coset projections

This file proves that `G ⧸ K → G ⧸ H` has a continuous section when `K ≤ H`
are closed subgroups of a profinite group. The proof uses compactness to
construct lower bounds for chains of section fibers and a maximality
argument.

It uses the Group Theory open-quotient theorem to show that closed coset
spaces are totally disconnected. It also proves that a surjective local
homeomorphism over a profinite space has a continuous section, and that
`G ⧸ T → G ⧸ S` is a local homeomorphism when `T` is open in `S`.

The local and global section theorems use their respective openness,
closedness and compactness hypotheses. They do not assert that arbitrary
surjections of topological groups split as homomorphisms.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, Exercise 4 (the
  maximal-pair approach to a continuous section). The proof here organizes the fibers
  differently.
- Mathlib, `Mathlib.Topology.Algebra.Group.Quotient`,
  `Mathlib.Topology.Algebra.ClopenNhdofOne` and
  `Mathlib.Topology.Algebra.ProperAction.Basic` (cosets and topology).
- Formal Frontier, *Group Theory*, `GroupTheory.Topology.OpenQuotient`
  (the open-quotient theorem, originally formalized in this library).
-/

@[expose] public section

open Function Set TopologicalSpace
open scoped Topology

universe u v

namespace QuotientGroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The coset space of a profinite group by a closed subgroup is totally
disconnected. -/
instance instTotallyDisconnectedSpace {S : Subgroup G} [IsClosed (S : Set G)] :
    TotallyDisconnectedSpace (G ⧸ S) :=
  Topology.IsOpenQuotientMap.totallyDisconnectedSpace
    QuotientGroup.isOpenQuotientMap_mk

end QuotientGroup

namespace IsLocalHomeomorph

/-- A surjective local homeomorphism over a profinite space has a continuous
section. -/
theorem exists_continuous_section_of_surjective
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B]
    {p : E → B} (hp : IsLocalHomeomorph p) (hsurj : Surjective p) :
    ∃ s : B → E, Continuous s ∧ RightInverse s p := by
  classical
  choose e he using hsurj
  let U : B → Opens B := fun y ↦
    ⟨(hp.localInverseAt (e y)).source, (hp.localInverseAt (e y)).open_source⟩
  have hyU (y : B) : y ∈ U y := by
    change y ∈ (hp.localInverseAt (e y)).source
    simpa only [he y] using hp.apply_self_mem_localInverseAt_source (x := e y)
  have hU : IsOpenCover U := IsOpenCover.of_sets
    (fun y ↦ (U y).isOpen) (eq_univ_of_forall fun y ↦ mem_iUnion.mpr ⟨y, hyU y⟩)
  obtain ⟨n, W, hWsub, hWcover, hWdisj⟩ :=
    hU.exists_finite_nonempty_disjoint_clopen_cover
  choose i hi using fun j ↦ (hWsub j).2
  let φ : ∀ j, C((W j : Set B), E) := fun j ↦
    ⟨fun x ↦ hp.localInverseAt (e (i j)) x,
      continuousOn_iff_continuous_domRestrict.mp
        ((hp.localInverseAt (e (i j))).continuousOn_toFun.mono (hi j))⟩
  have hφ (j k : Fin n) (x : B) (hxj : x ∈ (W j : Set B))
      (hxk : x ∈ (W k : Set B)) : φ j ⟨x, hxj⟩ = φ k ⟨x, hxk⟩ := by
    by_cases hjk : j = k
    · subst k
      rfl
    · have hd : Disjoint (W j : Set B) (W k : Set B) := by
        simpa only [← Clopens.coe_disjoint] using hWdisj hjk
      exact False.elim ((Set.disjoint_left.1 hd) hxj hxk)
  have hWnhds (x : B) : ∃ j, (W j : Set B) ∈ 𝓝 x := by
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hWcover (mem_univ x))
    exact ⟨j, (W j).isOpen.mem_nhds hxj⟩
  let s : C(B, E) := ContinuousMap.liftCover (fun j ↦ (W j : Set B)) φ hφ hWnhds
  refine ⟨s, s.continuous, fun x ↦ ?_⟩
  obtain ⟨j, hxj⟩ := mem_iUnion.mp (hWcover (mem_univ x))
  rw [show s x = φ j ⟨x, hxj⟩ by
    simpa only [s] using
      (ContinuousMap.liftCover_coe
        (S := fun j ↦ (W j : Set B)) (φ := φ) (hφ := hφ) (hS := hWnhds)
        ⟨x, hxj⟩)]
  exact hp.apply_localInverseAt_of_mem (hi j hxj)

end IsLocalHomeomorph

namespace Subgroup

/-- If `T` is open in `S`, the projection `G ⧸ T → G ⧸ S` is locally
injective. -/
theorem quotientMapOfLE_isLocallyInjective_of_isOpen
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {T S : Subgroup G} (hTS : T ≤ S) (hT : IsOpen (T.subgroupOf S : Set S)) :
    IsLocallyInjective (quotientMapOfLE hTS) := by
  rcases isOpen_induced_iff.mp hT with ⟨O, hOopen, hO⟩
  have hOneO : (1 : G) ∈ O := by
    have hOneT : (1 : S) ∈ (T.subgroupOf S : Set S) := (T.subgroupOf S).one_mem
    rw [← hO] at hOneT
    exact hOneT
  obtain ⟨V, hVopen, hOneV, hVV⟩ :=
    exists_open_nhds_one_mul_subset (hOopen.mem_nhds hOneO)
  let W : Set G := V ∩ V⁻¹
  have hWopen : IsOpen W := hVopen.inter hVopen.inv
  have hOneW : (1 : G) ∈ W := ⟨hOneV, by simpa using hOneV⟩
  intro q
  induction q using Quotient.inductionOn' with
  | _ g =>
      refine ⟨QuotientGroup.mk '' ((g * ·) '' W),
        QuotientGroup.isOpenMap_coe _ ((isOpenMap_mul_left g) W hWopen), ?_, ?_⟩
      · exact ⟨g * 1, ⟨1, hOneW, rfl⟩, by simp⟩
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩ hab
        apply QuotientGroup.eq.mpr
        have habS : a⁻¹ * b ∈ S := by
          have : (g * a)⁻¹ * (g * b) ∈ S :=
            QuotientGroup.eq.mp (by simpa using hab)
          simpa [mul_assoc] using this
        have hainvV : a⁻¹ ∈ V := by simpa [W] using ha.2
        have habO : a⁻¹ * b ∈ O := hVV ⟨a⁻¹, hainvV, b, hb.1, rfl⟩
        have habTsub : (⟨a⁻¹ * b, habS⟩ : S) ∈ (T.subgroupOf S : Set S) := by
          rw [← hO]
          exact habO
        change a⁻¹ * b ∈ T at habTsub
        simpa [mul_assoc] using habTsub

/-- If `T` is open in `S`, the projection `G ⧸ T → G ⧸ S` is a local
homeomorphism. -/
theorem quotientMapOfLE_isLocalHomeomorph_of_isOpen
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {T S : Subgroup G} (hTS : T ≤ S) (hT : IsOpen (T.subgroupOf S : Set S)) :
    IsLocalHomeomorph (quotientMapOfLE hTS) := by
  have hcont : Continuous (quotientMapOfLE hTS) := by
    exact continuous_id.quotient_map' fun a b hab ↦
      QuotientGroup.leftRel_apply.mpr (hTS (QuotientGroup.leftRel_apply.mp hab))
  have hopen : IsOpenMap (quotientMapOfLE hTS) := by
    apply (QuotientGroup.isOpenQuotientMap_mk (N := T)).isOpenMap_iff.mpr
    simpa [Function.comp_def] using (QuotientGroup.isOpenMap_coe (G := G) (N := S))
  have hlocinj := quotientMapOfLE_isLocallyInjective_of_isOpen hTS hT
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro q
  obtain ⟨U, hUopen, hqU, hUinj⟩ := hlocinj q
  refine ⟨U, hUopen.mem_nhds hqU,
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (hcont.comp continuous_subtype_val)
      (Set.injOn_iff_injective.mp hUinj)
      (hopen.comp hUopen.isOpenMap_subtype_val)⟩

/-- If `T` is open in `S` and `G ⧸ S` is profinite, the projection
`G ⧸ T → G ⧸ S` has a continuous section. -/
theorem quotientMapOfLE_exists_continuous_section_of_isOpen
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {T S : Subgroup G} [CompactSpace (G ⧸ S)] [T2Space (G ⧸ S)]
    [TotallyDisconnectedSpace (G ⧸ S)] (hTS : T ≤ S)
    (hT : IsOpen (T.subgroupOf S : Set S)) :
    ∃ s : (G ⧸ S) → (G ⧸ T), Continuous s ∧ RightInverse s (quotientMapOfLE hTS) := by
  apply (quotientMapOfLE_isLocalHomeomorph_of_isOpen hTS hT).exists_continuous_section_of_surjective
  intro q
  induction q using Quotient.inductionOn' with
  | _ g => exact ⟨QuotientGroup.mk g, rfl⟩

/-- If `S` is closed and `T` is open in `S`, the profinite coset projection
`G ⧸ T → G ⧸ S` has a continuous section. -/
theorem quotientMapOfLE_exists_continuous_section
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {T S : Subgroup G} [IsClosed (S : Set G)] (hTS : T ≤ S)
    (hT : IsOpen (T.subgroupOf S : Set S)) :
    ∃ s : (G ⧸ S) → (G ⧸ T), Continuous s ∧ RightInverse s (quotientMapOfLE hTS) :=
  quotientMapOfLE_exists_continuous_section_of_isOpen hTS hT

/-- Between a closed subgroup `K` and a strictly larger closed subgroup `S`
of a profinite group, there is a closed intermediate subgroup that is open
and proper in `S`. -/
theorem exists_intermediate_open_subgroupOf_of_lt
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {K S : Subgroup G} [IsClosed (K : Set G)] [IsClosed (S : Set G)] (hKS : K < S) :
    ∃ T : Subgroup G, K ≤ T ∧ T < S ∧ IsClosed (T : Set G) ∧
      IsOpen (T.subgroupOf S : Set S) := by
  obtain ⟨x, hxS, hxK⟩ := SetLike.exists_of_lt hKS
  let Kc : ClosedSubgroup G := ⟨K, inferInstance⟩
  have hKdesc := ProfiniteGrp.closedSubgroup_eq_sInf_open Kc
  have hex : ∃ N : Subgroup G, IsOpen (N : Set G) ∧ K ≤ N ∧ x ∉ N := by
    by_contra hn
    push Not at hn
    have hxinf : x ∈ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ Kc ≤ N} := by
      exact Subgroup.mem_sInf.mpr fun N hN ↦ hn N hN.1 hN.2
    have hxK' : x ∈ (Kc : Subgroup G) := by
      rw [hKdesc]
      exact hxinf
    change x ∈ K at hxK'
    exact hxK hxK'
  obtain ⟨N, hNopen, hKN, hxN⟩ := hex
  refine ⟨S ⊓ N, le_inf hKS.le hKN, ?_,
    IsClosed.inter (show IsClosed (S : Set G) from inferInstance)
      (N.isClosed_of_isOpen hNopen), ?_⟩
  · refine lt_of_le_of_ne inf_le_left fun hEq ↦ ?_
    have hxinf : x ∈ S ⊓ N := by rw [hEq]; exact hxS
    exact hxN hxinf.2
  · rw [Subgroup.inf_subgroupOf_left, Subgroup.coe_subgroupOf]
    exact hNopen.preimage continuous_subtype_val

/-- A continuous section through `G ⧸ S` can be strictly refined through an
intermediate closed subgroup whenever `K < S`. -/
theorem exists_strict_continuous_section_refinement
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {K S H : Subgroup G} [IsClosed (K : Set G)] [IsClosed (S : Set G)]
    (hKS : K < S) (hSH : S ≤ H) {s : (G ⧸ H) → (G ⧸ S)}
    (hscont : Continuous s) (hsright : RightInverse s (quotientMapOfLE hSH)) :
    ∃ (T : Subgroup G) (_hKT : K ≤ T) (hTS : T < S)
      (_hTclosed : IsClosed (T : Set G)),
      ∃ t : (G ⧸ H) → (G ⧸ T), Continuous t ∧
        RightInverse t (quotientMapOfLE (hTS.le.trans hSH)) ∧
        s = quotientMapOfLE hTS.le ∘ t := by
  obtain ⟨T, hKT, hTS, hTclosed, hTopen⟩ := exists_intermediate_open_subgroupOf_of_lt hKS
  let _ : IsClosed (T : Set G) := hTclosed
  obtain ⟨r, hrcont, hrright⟩ := quotientMapOfLE_exists_continuous_section hTS.le hTopen
  let t : (G ⧸ H) → (G ⧸ T) := r ∘ s
  refine ⟨T, hKT, hTS, hTclosed, t, hrcont.comp hscont, ?_, ?_⟩
  · intro x
    change quotientMapOfLE (hTS.le.trans hSH) (r (s x)) = x
    have hcomp (q : G ⧸ T) :
        quotientMapOfLE (hTS.le.trans hSH) q = quotientMapOfLE hSH (quotientMapOfLE hTS.le q) := by
      induction q using Quotient.inductionOn' with
      | _ g => rfl
    rw [hcomp, hrright (s x), hsright x]
  · funext x
    change s x = quotientMapOfLE hTS.le (r (s x))
    exact (hrright (s x)).symm

private def cosetSectionFiber
    {G : Type u} [Group G] {H S : Subgroup G} (s : (G ⧸ H) → (G ⧸ S)) :
    Set ((G ⧸ H) × G) :=
  {p | QuotientGroup.mk p.2 = s p.1}

private def HasContinuousCosetSection
    {G : Type u} [Group G] [TopologicalSpace G]
    (K H : Subgroup G) (R : Set ((G ⧸ H) × G)) : Prop :=
  ∃ (S : Subgroup G) (_hKS : K ≤ S) (hSH : S ≤ H)
    (s : (G ⧸ H) → (G ⧸ S)),
    IsClosed (S : Set G) ∧ Continuous s ∧
      RightInverse s (quotientMapOfLE hSH) ∧ R = cosetSectionFiber s

private theorem exists_continuous_section_iInf
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] {ι : Type v} (i₀ : ι) (S : ι → Subgroup G)
    (hSclosed : ∀ i, IsClosed (S i : Set G))
    {H : Subgroup G} (hSH : ∀ i, S i ≤ H)
    (s : ∀ i, (G ⧸ H) → (G ⧸ S i))
    (hscont : ∀ i, Continuous (s i))
    (hsright : ∀ i, RightInverse (s i) (quotientMapOfLE (hSH i)))
    (hsfiber : ∀ x, Directed (· ⊇ ·)
      (fun i ↦ {g | QuotientGroup.mk g = s i x})) :
    ∃ t : (G ⧸ H) → (G ⧸ ⨅ i, S i), Continuous t ∧
      RightInverse t (quotientMapOfLE (le_trans (iInf_le S i₀) (hSH i₀))) ∧
      ∀ i, s i = quotientMapOfLE (iInf_le S i) ∘ t := by
  classical
  let _ : Nonempty ι := ⟨i₀⟩
  let _ (i : ι) : IsClosed (S i : Set G) := hSclosed i
  let fiber (x : G ⧸ H) (i : ι) : Set G :=
    {g | QuotientGroup.mk g = s i x}
  have hfiber_nonempty (x : G ⧸ H) (i : ι) : (fiber x i).Nonempty := by
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (s i x)
    exact ⟨g, hg⟩
  have hfiber_closed (x : G ⧸ H) (i : ι) : IsClosed (fiber x i) := by
    exact isClosed_eq QuotientGroup.continuous_mk continuous_const
  have hfiber_directed (x : G ⧸ H) : Directed (· ⊇ ·) (fiber x) := by
    simpa only [fiber] using hsfiber x
  have hfiber_inter (x : G ⧸ H) : (⋂ i, fiber x i).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fiber x) (hfiber_directed x) (hfiber_nonempty x)
      (fun i ↦ (hfiber_closed x i).isCompact) (hfiber_closed x)
  choose lift hlift using hfiber_inter
  let t : (G ⧸ H) → (G ⧸ ⨅ i, S i) := fun x ↦ QuotientGroup.mk (lift x)
  have htcoord (i : ι) : s i = quotientMapOfLE (iInf_le S i) ∘ t := by
    funext x
    change s i x = QuotientGroup.mk (lift x)
    exact (mem_iInter.mp (hlift x) i).symm
  have hecont : Continuous (quotientiInfEmbedding S) := by
    apply continuous_pi
    intro i
    exact continuous_id.quotient_map' fun a b hab ↦
      QuotientGroup.leftRel_apply.mpr
        ((iInf_le S i) (QuotientGroup.leftRel_apply.mp hab))
  have hemb : Topology.IsClosedEmbedding (quotientiInfEmbedding S) :=
    hecont.isClosedEmbedding (quotientiInfEmbedding S).injective
  have htcont : Continuous t := hemb.isInducing.continuous_iff.mpr <| by
    apply continuous_pi
    intro i
    exact (hscont i).congr fun x ↦ by
      rw [congrFun (htcoord i) x]
      rfl
  refine ⟨t, htcont, ?_, htcoord⟩
  intro x
  have hcomp (q : G ⧸ ⨅ i, S i) :
      quotientMapOfLE (le_trans (iInf_le S i₀) (hSH i₀)) q =
        quotientMapOfLE (hSH i₀) (quotientMapOfLE (iInf_le S i₀) q) := by
    induction q using Quotient.inductionOn' with
    | _ g => rfl
  rw [hcomp]
  change quotientMapOfLE (hSH i₀) ((quotientMapOfLE (iInf_le S i₀) ∘ t) x) = x
  rw [← htcoord i₀]
  exact hsright i₀ x

private theorem exists_cosetSectionFiber_chain_lowerBound
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] {K H : Subgroup G} (c : Set (Set ((G ⧸ H) × G)))
    (hcP : c ⊆ {R | HasContinuousCosetSection K H R})
    (hchain : IsChain (· ⊆ ·) c) (hcne : c.Nonempty) :
    ∃ lb ∈ {R | HasContinuousCosetSection K H R}, ∀ R ∈ c, lb ⊆ R := by
  classical
  obtain ⟨R₀, hR₀⟩ := hcne
  have hdata (R : c) : HasContinuousCosetSection K H R := hcP R.2
  choose S hKS hSH s hs using hdata
  have hSclosed (R : c) : IsClosed (S R : Set G) := (hs R).1
  have hscont (R : c) : Continuous (s R) := (hs R).2.1
  have hsright (R : c) : RightInverse (s R) (quotientMapOfLE (hSH R)) :=
    (hs R).2.2.1
  have hReq (R : c) : (R : Set ((G ⧸ H) × G)) = cosetSectionFiber (s R) :=
    (hs R).2.2.2
  have hsfiber (x : G ⧸ H) : Directed (· ⊇ ·)
      (fun R ↦ {g | QuotientGroup.mk g = s R x}) := by
    intro R Q
    rcases hchain.total R.2 Q.2 with hRQ | hQR
    · refine ⟨R, Set.Subset.rfl, ?_⟩
      intro g hg
      have hmem : (x, g) ∈ (R : Set ((G ⧸ H) × G)) := by
        rw [hReq R]
        exact hg
      have := hRQ hmem
      rw [hReq Q] at this
      exact this
    · refine ⟨Q, ?_, Set.Subset.rfl⟩
      intro g hg
      have hmem : (x, g) ∈ (Q : Set ((G ⧸ H) × G)) := by
        rw [hReq Q]
        exact hg
      have := hQR hmem
      rw [hReq R] at this
      exact this
  obtain ⟨t, htcont, htright, htcoord⟩ :=
    exists_continuous_section_iInf
      (⟨R₀, hR₀⟩ : c) S hSclosed hSH s hscont hsright hsfiber
  refine ⟨cosetSectionFiber t, ?_, ?_⟩
  · change HasContinuousCosetSection K H (cosetSectionFiber t)
    refine ⟨⨅ R, S R, le_iInf hKS,
      (iInf_le S (⟨R₀, hR₀⟩ : c)).trans (hSH ⟨R₀, hR₀⟩), t, ?_,
      htcont, htright, rfl⟩
    simpa only [Subgroup.coe_iInf] using isClosed_iInter hSclosed
  · intro R hRc p hp
    let r : c := ⟨R, hRc⟩
    have hmem : p ∈ cosetSectionFiber (s r) := by
      change QuotientGroup.mk p.2 = s r p.1
      rw [congrFun (htcoord r) p.1]
      change QuotientGroup.mk p.2 = quotientMapOfLE (iInf_le S r) (t p.1)
      change QuotientGroup.mk p.2 = t p.1 at hp
      rw [← hp]
      rfl
    rw [← hReq r] at hmem
    exact hmem

/-- The projection between the left-coset spaces of two closed subgroups of a
profinite group has a continuous section.

This is Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, Exercise 4. The
proof follows its maximal-pair idea but organizes the fiber relations differently. -/
theorem quotientMapOfLE_exists_continuous_section_of_isClosed
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {K H : Subgroup G} [IsClosed (K : Set G)] [IsClosed (H : Set G)]
    (hKH : K ≤ H) :
    ∃ s : (G ⧸ H) → (G ⧸ K), Continuous s ∧
      RightInverse s (quotientMapOfLE hKH) := by
  classical
  let P : Set (Set ((G ⧸ H) × G)) :=
    {R | HasContinuousCosetSection K H R}
  let R₀ : Set ((G ⧸ H) × G) :=
    cosetSectionFiber (id : (G ⧸ H) → (G ⧸ H))
  have hright₀ : RightInverse (id : (G ⧸ H) → (G ⧸ H))
      (quotientMapOfLE (le_refl H)) := by
    intro x
    induction x using Quotient.inductionOn' with
    | _ g => rfl
  have hR₀P : R₀ ∈ P := by
    exact ⟨H, hKH, le_rfl, id, (show IsClosed (H : Set G) from inferInstance),
      continuous_id, hright₀, rfl⟩
  obtain ⟨Rmin, _, hRmin⟩ := zorn_superset_nonempty P
    (fun c hcP hchain hcne ↦
      exists_cosetSectionFiber_chain_lowerBound c hcP hchain hcne)
    R₀ hR₀P
  rcases hRmin.1 with ⟨S, hKS, hSH, s, hSclosed, hscont, hsright, hReq⟩
  have hSK : S ≤ K := by
    by_contra hnSK
    have hKSlt : K < S := lt_of_le_of_ne hKS fun hEq ↦ hnSK <| by rw [hEq]
    let _ : IsClosed (S : Set G) := hSclosed
    obtain ⟨T, hKT, hTS, hTclosed, t, htcont, htright, htcompat⟩ :=
      exists_strict_continuous_section_refinement hKSlt hSH hscont hsright
    let Rt : Set ((G ⧸ H) × G) := cosetSectionFiber t
    have hRtP : Rt ∈ P := by
      exact ⟨T, hKT, hTS.le.trans hSH, t, hTclosed, htcont, htright, rfl⟩
    have hRtRmin : Rt ⊆ Rmin := by
      intro p hp
      have hmem : p ∈ cosetSectionFiber s := by
        change QuotientGroup.mk p.2 = s p.1
        rw [congrFun htcompat p.1]
        change QuotientGroup.mk p.2 = quotientMapOfLE hTS.le (t p.1)
        change QuotientGroup.mk p.2 = t p.1 at hp
        rw [← hp]
        rfl
      rw [← hReq] at hmem
      exact hmem
    have hRt_strict : Rt ⊂ Rmin := by
      refine ⟨hRtRmin, ?_⟩
      intro hRminRt
      obtain ⟨a, haS, haT⟩ := SetLike.exists_of_lt hTS
      let x : G ⧸ H := QuotientGroup.mk 1
      obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (t x)
      have hgS : (QuotientGroup.mk g : G ⧸ S) = s x := by
        have hx := congrFun htcompat x
        change s x = quotientMapOfLE hTS.le (t x) at hx
        rw [hx, ← hg]
        rfl
      have hgaRmin : (x, g * a) ∈ Rmin := by
        rw [hReq]
        change QuotientGroup.mk (g * a) = s x
        rw [← hgS]
        apply QuotientGroup.eq.mpr
        simpa [mul_assoc] using haS
      have hgaRt := hRminRt hgaRmin
      change QuotientGroup.mk (g * a) = t x at hgaRt
      have hq : (QuotientGroup.mk g : G ⧸ T) = QuotientGroup.mk (g * a) :=
        hg.trans hgaRt.symm
      exact haT (by simpa [mul_assoc] using QuotientGroup.eq.mp hq)
    exact hRmin.not_ssubset hRtP hRt_strict
  have hSK_eq : S = K := le_antisymm hSK hKS
  subst S
  exact ⟨s, hscont, hsright⟩

end Subgroup
