/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.QuadraticRootOppositeBranch

/-!
# The constructed root charts form a disjoint cover

The localization inverse identifies the image of each actual root evaluation
with its complementary principal open. Thus the two actual chart maps cover
the quadratic spectrum, not merely a collection of abstract open subsets.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.QuadraticRootBranchLocalization
variable {R : Type*} [CommRing R] (a b r : R)
  (hr : r ^ 2 + a * r = b) (hu : IsUnit (r + r + a))

include hu in
/-- The image of actual root evaluation is its entire complementary principal open. -/
theorem evaluation_range :
    Set.range (PrimeSpectrum.comap (evaluation a b r hr).toRingHom) =
      (PrimeSpectrum.basicOpen (denominator a b r) : Set _) := by
  have he : (evaluation a b r hr).toRingHom =
      (branchEquiv a b r hr hu).toRingHom.comp
        (algebraMap (AdjoinRoot (polynomial a b)) (Branch a b r)) := by
    apply RingHom.ext
    intro z
    exact (branchEvaluation_base a b r hr hu z).symm
  have hs : Function.Surjective
      (PrimeSpectrum.comap (branchEquiv a b r hr hu).toRingHom) :=
    (PrimeSpectrum.comapEquiv (branchEquiv a b r hr hu).toRingEquiv).symm.surjective
  rw [he, PrimeSpectrum.comap_comp, Set.range_comp, hs.range_eq, Set.image_univ]
  exact PrimeSpectrum.localization_away_comap_range (Branch a b r) (denominator a b r)

include hu in
/-- Every point in the quadratic spectrum comes from one of the two constructed roots. -/
theorem rootCharts_cover (p : PrimeSpectrum (AdjoinRoot (polynomial a b))) :
    (∃ x : PrimeSpectrum R, PrimeSpectrum.comap (evaluation a b r hr).toRingHom x = p) ∨
      ∃ x : PrimeSpectrum R,
        PrimeSpectrum.comap (evaluation a b (oppositeRoot a r)
          (oppositeRoot_equation a b r hr)).toRingHom x = p := by
  change p ∈ Set.range (PrimeSpectrum.comap (evaluation a b r hr).toRingHom) ∨
    p ∈ Set.range (PrimeSpectrum.comap (evaluation a b (oppositeRoot a r)
      (oppositeRoot_equation a b r hr)).toRingHom)
  rw [evaluation_range a b r hr hu,
    evaluation_range a b (oppositeRoot a r) (oppositeRoot_equation a b r hr)
      (oppositeRoot_simple a r hu)]
  exact branch_cover a b r hu p

include hu in
/-- The actual root evaluations have disjoint images, including all nonreduced bases. -/
theorem rootCharts_disjoint :
    Disjoint (Set.range (PrimeSpectrum.comap (evaluation a b r hr).toRingHom))
      (Set.range (PrimeSpectrum.comap (evaluation a b (oppositeRoot a r)
        (oppositeRoot_equation a b r hr)).toRingHom)) := by
  rw [evaluation_range a b r hr hu,
    evaluation_range a b (oppositeRoot a r) (oppositeRoot_equation a b r hr)
      (oppositeRoot_simple a r hu)]
  apply Set.disjoint_left.mpr
  intro p h h'
  exact branch_disjoint a b r hr p ⟨h, h'⟩

end FLT.Mazur.QuadraticRootBranchLocalization
