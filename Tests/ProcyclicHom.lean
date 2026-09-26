/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicHom
public import ProfiniteGroups.ProcyclicRealization

/-!
# Procyclic homomorphism clients

Proof-using clients for prescribed images, quotient orders, and independent universes.
-/

@[expose] public section

open ProfiniteGrp
open Function

universe u v w

namespace ProcyclicHomTests

theorem arbitraryTarget (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) (h : H) :
    (∃! f : G →ₜ* H, f g = h) ↔
      ∀ p, primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator H h) p ≤
        hG.exponents p :=
  existsUnique_continuousHom_apply_generator_iff hG g hg h

theorem evaluationDeterminesMap (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (g : G) (hg : IsTopologicalGenerator G g) (f k : G →ₜ* H)
    (heq : f g = k g) : f = k :=
  continuousHom_ext_of_generator hg f k heq

theorem factorCommutes (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (h : H) (ha : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p) :
    (factorOfGenerator hG g hg h ha).comp (primewisePadicBaseMapOfGenerator G g) =
      primewisePadicBaseMapOfGenerator H h ∧
        factorOfGenerator hG g hg h ha g = h :=
  ⟨factorOfGenerator_comp_baseMap hG g hg h ha,
    factorOfGenerator_apply_generator hG g hg h ha⟩

theorem surjectionTest (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (h : H) (ha : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p) :
    Surjective (factorOfGenerator hG g hg h ha) ↔ IsTopologicalGenerator H h :=
  factorOfGenerator_surjective_iff hG g hg h ha

theorem quotientOrder (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (hH : IsProcyclic H) :
    (∃ f : G →ₜ* H, Surjective f) ↔ ∀ p, hH.exponents p ≤ hG.exponents p :=
  exists_surjective_continuousHom_iff_exponents_le hG hH

theorem positiveIndependentUniverses (G : ProfiniteGrp.{1}) (H : ProfiniteGrp.{2})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) (h : H)
    (ha : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p) :
    (factorOfGenerator hG g hg h ha).comp (primewisePadicBaseMapOfGenerator G g) =
      primewisePadicBaseMapOfGenerator H h :=
  factorOfGenerator_comp_baseMap hG g hg h ha

/-- A four-element profile supported at two. -/
def fourProfile (p : Nat.Primes) : ℕ∞ := if p.1 = 2 then 2 else 0
/-- A two-element profile supported at two. -/
def twoProfile (p : Nat.Primes) : ℕ∞ := if p.1 = 2 then 1 else 0

theorem finiteProfileQuotient :
    ∃ f : primewisePadicProcyclicModel.{1} fourProfile →ₜ*
      primewisePadicProcyclicModel.{2} twoProfile, Surjective f := by
  apply (exists_surjective_continuousHom_iff_exponents_le
    (primewisePadicProcyclicModel_isProcyclic fourProfile)
    (primewisePadicProcyclicModel_isProcyclic twoProfile)).mpr
  intro p
  simp only [primewisePadicProcyclicModel_exponents]
  unfold fourProfile twoProfile
  split_ifs <;> norm_num

theorem finiteProfileReverseImpossible :
    ¬ ∃ f : primewisePadicProcyclicModel.{2} twoProfile →ₜ*
      primewisePadicProcyclicModel.{1} fourProfile, Surjective f := by
  intro hf
  have hle := (exists_surjective_continuousHom_iff_exponents_le
    (primewisePadicProcyclicModel_isProcyclic twoProfile)
    (primewisePadicProcyclicModel_isProcyclic fourProfile)).mp hf
  have htwo := hle (⟨2, by decide⟩ : Nat.Primes)
  norm_num [primewisePadicProcyclicModel_exponents, fourProfile, twoProfile] at htwo

theorem targetIdentityAlways (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) :
    factorOfGenerator hG g hg (1 : H) (one_admissible hG g hg) = 1 :=
  factorOfGenerator_one hG g hg

theorem identityNeverSurjectsOntoCyclicTwo (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) :
    ¬ Surjective (factorOfGenerator hG g hg
      (1 : finiteCyclic 2) (one_admissible hG g hg)) := by
  intro hsurj
  rw [factorOfGenerator_one] at hsurj
  obtain ⟨x, hx⟩ := hsurj (finiteCyclicGenerator 2)
  have hneq : (finiteCyclicGenerator 2 : finiteCyclic 2) ≠ 1 := by
    intro heq
    exact (by decide : (1 : ZMod 2) ≠ 0) (congrArg Multiplicative.toAdd heq)
  exact hneq (by simpa using hx.symm)

/-- The finite Klein four-group, used as a potentially nonprocyclic target. -/
def klein : ProfiniteGrp :=
  ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 2 × ZMod 2)))

theorem kleinNotProcyclic : ¬ IsProcyclic klein := by
  let : Fintype klein := by
    change Fintype (Multiplicative (ZMod 2 × ZMod 2))
    infer_instance
  let : DiscreteTopology klein := Finite.instDiscreteTopology
  rintro ⟨g, hg⟩
  have hz2 (z : ZMod 2) : z + z = 0 := by
    fin_cases z <;> decide
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    change ((show Multiplicative (ZMod 2 × ZMod 2) from g).toAdd.1 +
      (show Multiplicative (ZMod 2 × ZMod 2) from g).toAdd.1,
      (show Multiplicative (ZMod 2 × ZMod 2) from g).toAdd.2 +
      (show Multiplicative (ZMod 2 × ZMod 2) from g).toAdd.2) = (0, 0)
    exact Prod.ext (hz2 _) (hz2 _)
  have hpowers : ∀ n : ℕ, g ^ n = 1 ∨ g ^ n = g := by
    intro n
    induction n with
    | zero => left; simp
    | succ n ih =>
      rcases ih with h | h
      · right; rw [pow_succ, h, one_mul]
      · left; rw [pow_succ, h]; simpa only [pow_two] using hg2
  have hsurj : Surjective (fun n : ℕ => g ^ n) := by
    have hpow := hg.denseRange_pow
    rwa [denseRange_iff_closure_range, closure_discrete, Set.range_eq_univ] at hpow
  let first : klein := Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2))
  let second : klein := Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2))
  have hfirst : first ≠ 1 := by
    intro heq
    have hc := congrArg (fun x : klein =>
      (show Multiplicative (ZMod 2 × ZMod 2) from x).toAdd.1) heq
    change (1 : ZMod 2) = 0 at hc
    exact (by decide : (1 : ZMod 2) ≠ 0) hc
  have hsecond : second ≠ 1 := by
    intro heq
    have hc := congrArg (fun x : klein =>
      (show Multiplicative (ZMod 2 × ZMod 2) from x).toAdd.2) heq
    change (1 : ZMod 2) = 0 at hc
    exact (by decide : (1 : ZMod 2) ≠ 0) hc
  have hdifferent : second ≠ first := by
    intro heq
    have hc := congrArg (fun x : klein =>
      (show Multiplicative (ZMod 2 × ZMod 2) from x).toAdd.1) heq
    change (0 : ZMod 2) = 1 at hc
    exact (by decide : (0 : ZMod 2) ≠ 1) hc
  have hthird : ∃ z : klein, z ≠ 1 ∧ z ≠ g := by
    by_cases hga : g = first
    · exact ⟨second, hsecond, by simpa only [hga] using hdifferent⟩
    · exact ⟨first, hfirst, Ne.symm hga⟩
  obtain ⟨z, hz1, hzg⟩ := hthird
  obtain ⟨n, hn⟩ := hsurj z
  rcases hpowers n with h | h
  · exact hz1 (hn.symm.trans h)
  · exact hzg (hn.symm.trans h)

theorem mapIntoFiniteNoncyclicTarget :
    ∃! f : finiteCyclic 4 →ₜ* klein,
      f (finiteCyclicGenerator 4) = 1 := by
  apply (existsUnique_continuousHom_apply_generator_iff
    (finiteCyclic_isProcyclic 4) (finiteCyclicGenerator 4)
    (finiteCyclicGenerator_isTopologicalGenerator 4) 1).mpr
  exact one_admissible (finiteCyclic_isProcyclic 4) (finiteCyclicGenerator 4)
    (finiteCyclicGenerator_isTopologicalGenerator 4)

/-- The endomorphism of the cyclic group of order four given by squaring. -/
def squareHom : finiteCyclic 4 →ₜ* finiteCyclic 4 :=
  { (AddMonoidHom.mulLeft (2 : ZMod 4)).toMultiplicative with
    continuous_toFun := by
      let : Finite (finiteCyclic 4) := by
        change Finite (Multiplicative (ZMod 4))
        infer_instance
      let : DiscreteTopology (finiteCyclic 4) := Finite.instDiscreteTopology
      exact continuous_of_discreteTopology }

theorem squareNotSurjective : ¬ Surjective squareHom := by
  let : Fintype (finiteCyclic 4) := by
    change Fintype (Multiplicative (ZMod 4))
    infer_instance
  intro hf
  obtain ⟨x, hx⟩ := hf (finiteCyclicGenerator 4)
  have heq := congrArg Multiplicative.toAdd hx
  change (2 : ZMod 4) * (show Multiplicative (ZMod 4) from x).toAdd = 1 at heq
  fin_cases x
  all_goals first
    | change (2 : ZMod 4) * 0 = 1 at heq
    | change (2 : ZMod 4) * 1 = 1 at heq
  all_goals norm_num at heq
  all_goals first
    | exact (by decide : (0 : ZMod 4) ≠ 1) heq
    | exact (by decide : (2 : ZMod 4) ≠ 1) heq

theorem squareAdmissible :
    ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator (finiteCyclic 4)
        (squareHom (finiteCyclicGenerator 4))) p ≤
      (finiteCyclic_isProcyclic 4).exponents p := by
  let h := squareHom (finiteCyclicGenerator 4)
  apply (existsUnique_continuousHom_apply_generator_iff
    (finiteCyclic_isProcyclic 4) (finiteCyclicGenerator 4)
    (finiteCyclicGenerator_isTopologicalGenerator 4) h).mp
  refine ⟨squareHom, rfl, ?_⟩
  intro f hf
  exact continuousHom_ext_of_generator
    (finiteCyclicGenerator_isTopologicalGenerator 4) _ _ hf

theorem squareImageNotOnto :
    ¬ Surjective (factorOfGenerator (finiteCyclic_isProcyclic 4)
        (finiteCyclicGenerator 4)
        (finiteCyclicGenerator_isTopologicalGenerator 4)
        (squareHom (finiteCyclicGenerator 4)) squareAdmissible) := by
  have heq : factorOfGenerator (finiteCyclic_isProcyclic 4)
      (finiteCyclicGenerator 4)
      (finiteCyclicGenerator_isTopologicalGenerator 4)
      (squareHom (finiteCyclicGenerator 4)) squareAdmissible = squareHom :=
    continuousHom_ext_of_generator (finiteCyclicGenerator_isTopologicalGenerator 4)
      _ _ (factorOfGenerator_apply_generator _ _ _ _ _)
  simpa [heq] using squareNotSurjective

theorem zeroSourceToZeroTarget :
    ∃! f : primewisePadicProcyclicModel.{1} (fun _ => (0 : ℕ∞)) →ₜ*
      primewisePadicProcyclicModel.{2} (fun _ => (0 : ℕ∞)),
      f (primewisePadicRealizationGenerator (fun _ => (0 : ℕ∞))) = 1 := by
  apply (existsUnique_continuousHom_apply_generator_iff
    (primewisePadicProcyclicModel_isProcyclic (fun _ => (0 : ℕ∞)))
    (primewisePadicRealizationGenerator (fun _ => (0 : ℕ∞)))
    (primewisePadicRealizationGenerator_isTopologicalGenerator _) 1).mpr
  exact one_admissible
    (primewisePadicProcyclicModel_isProcyclic (fun _ => (0 : ℕ∞)))
    (primewisePadicRealizationGenerator (fun _ => (0 : ℕ∞)))
    (primewisePadicRealizationGenerator_isTopologicalGenerator _)

theorem topSourceToArbitrary (H : ProfiniteGrp.{v}) (h : H) :
    ∃! f : primewisePadicProcyclicModel.{1} (fun _ => (⊤ : ℕ∞)) →ₜ* H,
      f (primewisePadicRealizationGenerator (fun _ => (⊤ : ℕ∞))) = h := by
  apply (existsUnique_continuousHom_apply_generator_iff
    (primewisePadicProcyclicModel_isProcyclic (fun _ => (⊤ : ℕ∞)))
    (primewisePadicRealizationGenerator (fun _ => (⊤ : ℕ∞)))
    (primewisePadicRealizationGenerator_isTopologicalGenerator _) h).mpr
  simpa only [primewisePadicProcyclicModel_exponents] using
    (fun p : Nat.Primes => le_top : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ (⊤ : ℕ∞))

/-- A profile with zero, positive finite and infinite primewise coordinates. -/
def mixedProfile (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then 0 else if p.1 = 3 then 2 else ⊤
/-- A smaller profile used to test the direction of the Hom inequality. -/
def smallerMixedProfile (p : Nat.Primes) : ℕ∞ :=
  if p.1 = 2 then 0 else if p.1 = 3 then 1 else ⊤

theorem mixedProfileQuotient :
    ∃ f : primewisePadicProcyclicModel.{1} mixedProfile →ₜ*
      primewisePadicProcyclicModel.{2} smallerMixedProfile, Surjective f := by
  apply (exists_surjective_continuousHom_iff_exponents_le
    (primewisePadicProcyclicModel_isProcyclic mixedProfile)
    (primewisePadicProcyclicModel_isProcyclic smallerMixedProfile)).mpr
  intro p
  simp only [primewisePadicProcyclicModel_exponents]
  unfold mixedProfile smallerMixedProfile
  split_ifs <;> norm_num

theorem identityAndComposition (G : ProfiniteGrp.{u}) (H : ProfiniteGrp.{v})
    (K : ProfiniteGrp.{w}) (hG : IsProcyclic G) (hH : IsProcyclic H)
    (g : G) (hg : IsTopologicalGenerator G g) (h : H)
    (hh : IsTopologicalGenerator H h) (k : K)
    (ha : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p)
    (hb : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator K k) p ≤ hH.exponents p) :
    (factorOfGenerator hH h hh k hb).comp
        (factorOfGenerator hG g hg h ha) =
        factorOfGenerator hG g hg k (fun p =>
          (hb p).trans (by simpa only [hH.exponents_eq_baseMap_of_generator h hh]
            using (ha p))) :=
  factorOfGenerator_comp hG g hg hH h hh k ha hb

theorem identityEvaluation (G : ProfiniteGrp.{u})
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) :
    factorOfGenerator hG g hg g
      (by
        intro p
        rw [hG.exponents_eq_baseMap_of_generator g hg]) =
      ContinuousMonoidHom.id G :=
  factorOfGenerator_self hG g hg _

end ProcyclicHomTests
