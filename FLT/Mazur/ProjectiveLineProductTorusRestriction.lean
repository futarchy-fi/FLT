/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineProductTorusExt
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# Relative torus restriction determines parameterized projective-line maps

The overlap factors through the actual product with the torus. Its previously
proved density therefore gives a morphism comparison in the over-category.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Polynomial LaurentPolynomial
namespace FLT.Mazur.ProjectiveLineProductCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K S : Type u) [Field K] [CommRing S] [IsDomain S] [Algebra K S]
local notation "P" => Over.mk (parameterToBase K S)
local notation "L" => PolygonPinching.component K
local notation "T" => MultiplicativeGroupScheme.gm K
local notation "j" => PolygonPinching.torusToComponent K
local notation "o" => ProjectiveLineProductOverlap.left S ≫ productChartMap K S false

omit [IsDomain S] in
/-- The overlap's second projection is its actual Laurent coefficient point. -/
@[reassoc] theorem productOverlap_snd :
    o ≫ pullback.snd (parameterToBase K S) (ProjectiveLine.toBase K) =
      ProjectiveLineProductOverlap.coeff K S ≫ (j).left := by
  rw [Category.assoc, productChartMap_snd, ← Category.assoc,
    ProjectiveLineProductOverlap.left_coeff, Category.assoc]
  rfl

/-- The product with the full torus detects relative maps from the complete projective line. -/
theorem product_hom_ext_torus {Y : Over (Spec (.of K))} [IsSeparated Y.hom]
    (f g : P ⊗ L ⟶ Y) (h : P ◁ j ≫ f = P ◁ j ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply product_hom_ext_overlap K S Y.hom f.left g.left (f.w.trans g.w.symm)
  let a := o ≫ pullback.fst (parameterToBase K S) (ProjectiveLine.toBase K)
  let b := ProjectiveLineProductOverlap.coeff K S
  have hab : a ≫ (P).hom = b ≫ (T).hom := by
    rw [← (j).w, ← Category.assoc, ← productOverlap_snd]
    exact Category.assoc _ _ _ |>.trans
      ((congrArg (o ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
  let t := pullback.lift a b hab
  have ht : t ≫ (P ◁ j).left = o := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      erw [Over.whiskerLeft_left_fst, pullback.lift_fst]
      rfl
    · rw [Category.assoc]
      erw [Over.whiskerLeft_left_snd, pullback.lift_snd_assoc]
      exact (productOverlap_snd K S).symm
  have he := congrArg (fun m => t ≫ m.left) h
  simpa only [Over.comp_left, ← Category.assoc, ht] using he

end FLT.Mazur.ProjectiveLineProductCharts
