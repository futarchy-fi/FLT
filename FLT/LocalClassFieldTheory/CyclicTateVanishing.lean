/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TateNormVanishing
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.FiniteCyclic

/-!
# The cyclic adjacent-vanishing criterion

For a finite cyclic group, Tate vanishing in degrees zero and one implies
vanishing in every integer degree. The periodic resolutions handle nonzero
ordinary degrees; explicit norm-splice arguments cover zero and minus one.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology groupHomology Rep.FiniteCyclicGroup

section Generator

variable {k G : Type} [CommRing k] [CommGroup G] [Fintype G]
  (M : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include hg

/-- Vanishing in degree zero makes the cyclic norm-then-difference complex exact. -/
theorem cyclic_even_exact_of_tate_zero (h : Limits.IsZero (tateCohomology M 0)) :
    (normHomCompSub M g).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hinv := (Representation.mem_invariants_iff_of_forall_mem_zpowers
    M.ρ g hg x).2 (sub_eq_zero.mp hx)
  apply norm_surjective_of_tate_zero M h x
  ext a
  exact sub_eq_zero.mpr (hinv a)

/-- Vanishing in degree one makes the cyclic difference-then-norm complex exact. -/
theorem cyclic_odd_exact_of_tate_one (h : Limits.IsZero (tateCohomology M 1)) :
    (subCompNormHom M g).Exact := by
  apply (ShortComplex.exact_iff_isZero_homology _).mpr
  exact h.of_iso (((TateCohomology.isoGroupCohomology 1).app M) ≪≫
    groupCohomologyIsoOdd M g hg 1 (by decide)).symm

/-- The odd periodic exactness also kills the norm splice in degree minus one. -/
theorem cyclic_tate_neg_one_isZero (h : Limits.IsZero (tateCohomology M 1)) :
    Limits.IsZero (tateCohomology M (-1)) := by
  classical
  apply tate_neg_one_isZero_of_augmentation_exact M
  intro x hx
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (cyclic_odd_exact_of_tate_one M g hg h) x hx
  refine ⟨Finsupp.single g⁻¹ y, ?_⟩
  change M.ρ g y - y = x at hy
  exact (d₁₀_single M g⁻¹ y).trans (by simpa only [inv_inv] using hy)

/-- The cyclic criterion, with a specified generator, covers every integer degree. -/
theorem cyclic_tate_isZero_of_generator
    (h₀ : Limits.IsZero (tateCohomology M 0))
    (h₁ : Limits.IsZero (tateCohomology M 1)) (n : ℤ) :
    Limits.IsZero (tateCohomology M n) := by
  classical
  have he := (ShortComplex.exact_iff_isZero_homology _).mp
    (cyclic_even_exact_of_tate_zero M g hg h₀)
  have ho := (ShortComplex.exact_iff_isZero_homology _).mp
    (cyclic_odd_exact_of_tate_one M g hg h₁)
  rcases n with n | n
  · cases n with
    | zero => exact h₀
    | succ n =>
      apply Limits.IsZero.of_iso _ ((TateCohomology.isoGroupCohomology (n + 1)).app M)
      rcases Nat.even_or_odd (n + 1) with hn | hn
      · exact he.of_iso (groupCohomologyIsoEven M g hg (n + 1) hn)
      · exact ho.of_iso (groupCohomologyIsoOdd M g hg (n + 1) hn)
  · cases n with
    | zero => exact cyclic_tate_neg_one_isZero M g hg h₁
    | succ n =>
      apply Limits.IsZero.of_iso _
        ((TateCohomology.isoGroupHomology _ (n + 1) (by omega)).app M)
      rcases Nat.even_or_odd (n + 1) with hn | hn
      · exact ho.of_iso (groupHomologyIsoEven M g hg (n + 1) hn)
      · exact he.of_iso (groupHomologyIsoOdd M g hg (n + 1) hn)

end Generator

/-- A finite cyclic group needs only the two adjacent vanishing groups. -/
theorem cyclic_tate_isZero_of_adjacent {k G : Type} [CommRing k] [Group G] [Fintype G]
    [IsCyclic G] (M : Rep k G) (h₀ : Limits.IsZero (tateCohomology M 0))
    (h₁ : Limits.IsZero (tateCohomology M 1)) (n : ℤ) :
    Limits.IsZero (tateCohomology M n) := by
  let := IsCyclic.commGroup (α := G)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact cyclic_tate_isZero_of_generator M g hg h₀ h₁ n

end LocalClassFieldTheory
