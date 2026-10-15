/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.QuadraticRootBranchChart

/-!
# The opposite quadratic branch and the two-branch cover

A simple root determines its opposite root without a second lifting choice.
The two complementary principal opens are disjoint and cover the whole
quadratic spectrum over the original, possibly nonreduced, coefficient ring.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.QuadraticRootBranchLocalization
variable {R : Type*} [CommRing R] (a b r : R)
  (hr : r ^ 2 + a * r = b) (hu : IsUnit (r + r + a))

/-- The other root of the same original quadratic. -/
def oppositeRoot : R := -r - a

include hr in
/-- The opposite root satisfies the unchanged quadratic equation. -/
theorem oppositeRoot_equation : oppositeRoot a r ^ 2 + a * oppositeRoot a r = b := by
  dsimp only [oppositeRoot]
  linear_combination hr

include hu in
/-- The opposite root has the same invertible separation, with reversed sign. -/
theorem oppositeRoot_simple :
    IsUnit (oppositeRoot a r + oppositeRoot a r + a) := by
  convert hu.neg using 1
  dsimp only [oppositeRoot]
  ring

/-- Reversing the root choice twice recovers the original root. -/
@[simp] theorem oppositeRoot_involutive : oppositeRoot a (oppositeRoot a r) = r := by
  dsimp only [oppositeRoot]
  ring

include hr in
/-- The two complementary branch denominators multiply to zero in the original algebra. -/
theorem denominator_mul_opposite :
    denominator a b r * denominator a b (oppositeRoot a r) = 0 := by
  let A := AdjoinRoot (polynomial a b)
  let v : A := AdjoinRoot.root (polynomial a b)
  have he : v ^ 2 + algebraMap R A a * v = algebraMap R A b := by
    have h := AdjoinRoot.eval₂_root (polynomial a b)
    change (X ^ 2 + C a * X - C b).eval₂ (algebraMap R A) v = 0 at h
    simpa only [eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_mul,
      eval₂_C, sub_eq_zero] using h
  have hr' := congrArg (algebraMap R A) hr
  simp only [map_add, map_pow, map_mul] at hr'
  change (v + algebraMap R A (r + a)) *
    (v + algebraMap R A (-r - a + a)) = 0
  simp only [map_add, map_sub, map_neg]
  linear_combination he - hr'

/-- The two denominators differ by the original root separation. -/
theorem denominator_sub_opposite :
    denominator a b r - denominator a b (oppositeRoot a r) =
      algebraMap R _ (r + r + a) := by
  simp only [denominator, oppositeRoot, map_add, map_sub, map_neg]
  ring

include hu in
/-- Every point belongs to at least one of the two branch principal opens. -/
theorem branch_cover (p : PrimeSpectrum (AdjoinRoot (polynomial a b))) :
    denominator a b r ∉ p.asIdeal ∨ denominator a b (oppositeRoot a r) ∉ p.asIdeal := by
  by_contra h
  push Not at h
  have hm := p.asIdeal.sub_mem h.1 h.2
  rw [denominator_sub_opposite] at hm
  exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem hm (hu.map (algebraMap R _)))

include hr in
/-- No point lies on both principal branches. -/
theorem branch_disjoint (p : PrimeSpectrum (AdjoinRoot (polynomial a b))) :
    ¬ (denominator a b r ∉ p.asIdeal ∧
      denominator a b (oppositeRoot a r) ∉ p.asIdeal) := by
  rintro ⟨h, h'⟩
  have hm : denominator a b r * denominator a b (oppositeRoot a r) ∈ p.asIdeal := by
    rw [denominator_mul_opposite a b r hr]
    exact p.asIdeal.zero_mem
  exact (p.isPrime.mem_or_mem hm).elim h h'

/-- The full opposite principal branch is the original base, with a proved inverse. -/
def oppositeBranchEquiv : Branch a b (oppositeRoot a r) ≃ₐ[R] R :=
  branchEquiv a b (oppositeRoot a r) (oppositeRoot_equation a b r hr)
    (oppositeRoot_simple a r hu)

include hu in
/-- The opposite root gives an actual open immersion into the same quadratic spectrum. -/
theorem oppositeBranchChart_isOpenImmersion :
    IsOpenImmersion (branchChart a b (oppositeRoot a r) (oppositeRoot_equation a b r hr)) :=
  branchChart_isOpenImmersion a b (oppositeRoot a r) (oppositeRoot_equation a b r hr)
    (oppositeRoot_simple a r hu)

end FLT.Mazur.QuadraticRootBranchLocalization
