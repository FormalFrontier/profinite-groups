/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.CompatibleSylow
public import Mathlib.Algebra.Group.PUnit

public section

set_option warningAsError true

/-! # Prescribed compatible Sylow families and their finite-quotient images -/

open CategoryTheory

universe u

example (G : ProfiniteGrp.{u}) (p : ℕ) (hp : p.Prime)
    (U : OpenNormalSubgroup G) (P : Sylow p (G ⧸ (U : Subgroup G))) :
    ∃ s : G.CompatibleSylowFamily p hp, s.at U = P := by
  exact G.exists_compatibleSylowFamily_with p hp U P

example (G : ProfiniteGrp.{u}) (p : ℕ) (hp : p.Prime)
    (s : G.CompatibleSylowFamily p hp) {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (s.at U : Subgroup (G ⧸ (U : Subgroup G))).map
      (QuotientGroup.map (U : Subgroup G) (V : Subgroup G) (MonoidHom.id G) h) =
        (s.at V : Subgroup (G ⧸ (V : Subgroup G))) :=
  s.map_at_subgroup h

example (G : ProfiniteGrp.{u}) (p : ℕ) (hp : p.Prime)
    (s t : G.CompatibleSylowFamily p hp)
    (h : ∀ U : OpenNormalSubgroup G,
      (s.at U : Subgroup (G ⧸ (U : Subgroup G))) = (t.at U : Subgroup _)) :
    s = t := by
  apply ProfiniteGrp.CompatibleSylowFamily.ext
  intro U
  exact Sylow.ext (h U)

example (p : ℕ) (hp : p.Prime) :
    Nonempty ((ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit)).CompatibleSylowFamily p hp) :=
  (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of PUnit)).exists_compatibleSylowFamily p hp

example (p : ℕ) (hp : p.Prime) (U : OpenNormalSubgroup (ProfiniteGrp.of PUnit)) :
    ∃ s : (ProfiniteGrp.of PUnit).CompatibleSylowFamily p hp,
      (s.at U : Subgroup ((ProfiniteGrp.of PUnit) ⧸ (U : Subgroup (ProfiniteGrp.of PUnit)))) =
        ⊤ := by
  let G := ProfiniteGrp.of PUnit
  let P : Sylow p (G ⧸ (U : Subgroup G)) := Sylow.nonempty.some
  have hquot : Subsingleton (G ⧸ (U : Subgroup G)) :=
    QuotientGroup.mk_surjective.subsingleton
  have hP : (P : Subgroup (G ⧸ (U : Subgroup G))) = ⊤ := by
    apply (Subgroup.eq_top_iff' _).mpr
    intro q
    have hq : q = 1 := hquot.elim q 1
    rw [hq]
    exact Subgroup.one_mem _
  obtain ⟨s, hs⟩ := G.exists_compatibleSylowFamily_with p hp U P
  refine ⟨s, ?_⟩
  have hs' : s.at U = P := hs
  exact (congrArg (fun Q : Sylow p (G ⧸ (U : Subgroup G)) =>
    (Q : Subgroup (G ⧸ (U : Subgroup G)))) hs').trans hP
