/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenCoverGluingIso
/-!
# Common affine refinements of arbitrary affine tests

Pulling an open cover back to an affine test and then refining it gives a covering family
with explicit ring coordinates in both the test and the original covering charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.AffineOpenCoverCommonRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (U : X.AffineOpenCover)
variable {A : CommRingCat.{u}} (f : Spec A ⟶ X)

/-- Pull back the open cover to an arbitrary affine test and refine it by affines. -/
def testCover : (Spec A).AffineOpenCover :=
  Scheme.OpenCover.affineRefinement (U.openCover.pullback₁ f)

/-- The common map from a member of the pulled-back cover into the original scheme. -/
def testMap (i : (testCover U f).I₀) : Spec ((testCover U f).X i) ⟶ X :=
  (testCover U f).f i ≫ f

/-- The original chart containing a member of the pulled-back cover. -/
def testIndex (i : (testCover U f).I₀) : U.I₀ := i.1

/-- The coordinates of a pulled-back chart in the arbitrary affine test. -/
def testSource (i : (testCover U f).I₀) : A ⟶ (testCover U f).X i :=
  Spec.preimage ((testCover U f).f i)

/-- The independent coordinates in the original affine covering chart. -/
def testTarget (i : (testCover U f).I₀) : U.X (testIndex U f i) ⟶ (testCover U f).X i :=
  Spec.preimage (((U.openCover.pullback₁ f).X i.1).affineCover.f i.2 ≫
    Limits.pullback.snd f (U.f i.1))

/-- Source coordinates recover the actual covering map on the affine test. -/
theorem testSource_spec (i : (testCover U f).I₀) :
    Spec.map (testSource U f i) = (testCover U f).f i := Spec.map_preimage _

/-- The pulled-back source triangle commutes. -/
theorem testSource_over (i : (testCover U f).I₀) :
    Spec.map (testSource U f i) ≫ f = testMap U f i := by
  rw [testSource_spec]
  rfl

/-- The original-cover triangle commutes as well. -/
theorem testTarget_over (i : (testCover U f).I₀) :
    Spec.map (testTarget U f i) ≫ U.f (testIndex U f i) = testMap U f i := by
  unfold testTarget
  rw [Spec.map_preimage]
  change (_ ≫ Limits.pullback.snd f (U.f i.1)) ≫ U.f i.1 =
    (_ ≫ Limits.pullback.fst f (U.f i.1)) ≫ f
  rw [Category.assoc, Category.assoc, Limits.pullback.condition]

/-- The affine refinements cover every point of the arbitrary test. -/
theorem testCover_covers (x : Spec A) :
    ∃ i, x ∈ Set.range ((testCover U f).f i) := jointly_surjective _ x

end FLT.Mazur.AffineOpenCoverCommonRefinement
