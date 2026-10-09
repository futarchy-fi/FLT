/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisTupleAffineComparison

/-!
# Change of tuple on arbitrary scheme tests

Affine covers detect both the transition domain and equality of the actual
classifying morphisms. The source test scheme need not be affine.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable {X : Scheme.{u}}
variable (f : X ⟶ polynomialBasisScheme R I d w S J)
variable (g : X ⟶ polynomialBasisScheme R I d v S J)
variable (h : f ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) =
  g ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d v S J))

include g h in
/-- The first parameter lands in the transition domain on every common scheme test. -/
theorem intrinsicChartMorphism_tupleRange :
    Set.range (f ≫ intrinsicChartMorphism R I d w S J) ⊆
      Set.range (chartTupleTransitionOpen R I d w v).ι := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := X.affineOpenCover.covers x
  let i := X.affineOpenCover.idx x
  obtain ⟨k, hk, _⟩ := intrinsicChartMorphism_affineTupleComparison_over R I d w v S J
    (X.affineOpenCover.X i) (X.affineOpenCover.f i ≫ f) (X.affineOpenCover.f i ≫ g)
    (by simpa only [Category.assoc] using congrArg (X.affineOpenCover.f i ≫ ·) h)
  refine ⟨k y, ?_⟩
  change (k ≫ (chartTupleTransitionOpen R I d w v).ι) y = _
  rw [hk]
  change intrinsicChartMorphism R I d w S J (f (X.affineOpenCover.f i y)) = _
  rw [show X.affineOpenCover.f i y = x from hy]
  rfl

/-- The actual factorization of a common test through the transition domain. -/
def intrinsicTupleComparison : X ⟶ (chartTupleTransitionOpen R I d w v).toScheme :=
  IsOpenImmersion.lift (chartTupleTransitionOpen R I d w v).ι
    (f ≫ intrinsicChartMorphism R I d w S J)
    (intrinsicChartMorphism_tupleRange R I d w v S J f g h)

/-- The transition factorization recovers the first intrinsic parameter. -/
theorem intrinsicTupleComparison_ι :
    intrinsicTupleComparison R I d w v S J f g h ≫ (chartTupleTransitionOpen R I d w v).ι =
      f ≫ intrinsicChartMorphism R I d w S J :=
  IsOpenImmersion.lift_fac _ _ _

/-- Changing tuple on an arbitrary scheme test recovers its second intrinsic parameter. -/
theorem intrinsicTupleComparison_transition :
    intrinsicTupleComparison R I d w v S J f g h ≫ chartTupleTransition R I d w v =
      g ≫ intrinsicChartMorphism R I d v S J := by
  apply X.affineOpenCover.openCover.hom_ext
  intro i
  change X.affineOpenCover.f i ≫ _ = X.affineOpenCover.f i ≫ _
  obtain ⟨k, hk, ht⟩ := intrinsicChartMorphism_affineTupleComparison_over R I d w v S J
    (X.affineOpenCover.X i) (X.affineOpenCover.f i ≫ f) (X.affineOpenCover.f i ≫ g)
    (by simpa only [Category.assoc] using congrArg (X.affineOpenCover.f i ≫ ·) h)
  have he : X.affineOpenCover.f i ≫ intrinsicTupleComparison R I d w v S J f g h = k := by
    rw [← cancel_mono (chartTupleTransitionOpen R I d w v).ι, Category.assoc,
      intrinsicTupleComparison_ι, hk, Category.assoc]
  simpa only [Category.assoc] using (congrArg (· ≫ chartTupleTransition R I d w v) he).trans ht

end FLT.Mazur.HilbertChart
