/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOverlapMapNormalization

/-!
# Glued comparisons on arbitrary scheme tests

A pair of coordinates with the same base map determines a normalized pullback
of the glued overlap isomorphism. Its affine restrictions are the effective maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
attribute [local irreducible] sheaf CrossRefinement.effectiveComparison baseOverlapComparison

/-- Pull the actual glued overlap map back along a pair of test coordinates. -/
def schemeTestComparison (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (w : i ≫ C.base = j ≫ C'.base) :
    (pullback i).obj (C.sheaf D) ⟶ (pullback j).obj (C'.sheaf D) :=
  C.normalizedOverlapMap C' D (Limits.pullback.lift i j w) i j
    (Limits.pullback.lift_fst i j w) (Limits.pullback.lift_snd i j w)

/-- The test comparison is an isomorphism. -/
instance schemeTestComparison_isIso (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (w : i ≫ C.base = j ≫ C'.base) : IsIso (C.schemeTestComparison C' D i j w) := by
  unfold schemeTestComparison
  infer_instance

/-- Affine tests recover the independently constructed effective comparison. -/
theorem schemeTestComparison_affine {A : CommRingCat.{u}}
    (i : Spec A ⟶ Spec C.baseRing) (j : Spec A ⟶ Spec C'.baseRing)
    (w : i ≫ C.base = j ≫ C'.base) :
    C.schemeTestComparison C' D i j w = (C.affineTestComparison C' i j w D).hom :=
  C.normalizedOverlapMap_affine C' D _ i j _ _ w

/-- Every affine restriction of a scheme test comparison is its effective comparison. -/
theorem schemeTestComparison_affine_refine {A : CommRingCat.{u}} (t : Spec A ⟶ W)
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (w : i ≫ C.base = j ≫ C'.base) :
    (pullback t).map (C.schemeTestComparison C' D i j w) ≫
        (pullbackComp t j).hom.app (C'.sheaf D) =
      (pullbackComp t i).hom.app (C.sheaf D) ≫
        (C.affineTestComparison C' (t ≫ i) (t ≫ j)
          (by simpa only [Category.assoc] using congrArg (t ≫ ·) w) D).hom := by
  have hi : (t ≫ Limits.pullback.lift i j w) ≫ Limits.pullback.fst C.base C'.base =
      t ≫ i := by rw [Category.assoc, Limits.pullback.lift_fst]
  have hj : (t ≫ Limits.pullback.lift i j w) ≫ Limits.pullback.snd C.base C'.base =
      t ≫ j := by rw [Category.assoc, Limits.pullback.lift_snd]
  have hn := SheafPullbackMapNormalization.normalize_refine
    (Limits.pullback.lift i j w) (Limits.pullback.fst C.base C'.base)
    (Limits.pullback.snd C.base C'.base) i j
    (Limits.pullback.lift_fst i j w) (Limits.pullback.lift_snd i j w)
    t (t ≫ Limits.pullback.lift i j w) rfl (t ≫ i) (t ≫ j) rfl rfl hi hj
    (C.baseOverlapComparison C' D).hom
  change (pullback t).map (C.schemeTestComparison C' D i j w) ≫ _ =
    _ ≫ C.normalizedOverlapMap C' D _ _ _ hi hj at hn
  rw [C.normalizedOverlapMap_affine C' D _ _ _ hi hj
    (by simpa only [Category.assoc] using congrArg (t ≫ ·) w)] at hn
  simpa only [SheafPullbackPathComparison.comparison, pullbackCongr,
    eqToIso_refl, Iso.trans_refl] using hn

end FLT.Mazur.SchemeAffineDescent.Chart
