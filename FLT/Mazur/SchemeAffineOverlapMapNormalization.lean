/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOverlapTestNormalization
public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Normalized overlap maps on arbitrary test schemes

The glued pair comparison can be expressed in any chosen coordinate paths.
On affine tests it recovers the effective comparison in those coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open SheafPullbackMapNormalization SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
attribute [local irreducible] sheaf CrossRefinement.effectiveComparison baseOverlapComparison

/-- Normalize the glued pair comparison to specified paths on a test scheme. -/
def normalizedOverlapMap (c : W ⟶ C.baseOverlap C')
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : c ≫ Limits.pullback.fst C.base C'.base = i)
    (hj : c ≫ Limits.pullback.snd C.base C'.base = j) :
    (pullback i).obj (C.sheaf D) ⟶ (pullback j).obj (C'.sheaf D) :=
  normalize c (Limits.pullback.fst C.base C'.base) (Limits.pullback.snd C.base C'.base)
    i j hi hj (C.baseOverlapComparison C' D).hom

/-- The normalized comparison remains invertible. -/
instance normalizedOverlapMap_isIso (c : W ⟶ C.baseOverlap C')
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : c ≫ Limits.pullback.fst C.base C'.base = i)
    (hj : c ≫ Limits.pullback.snd C.base C'.base = j) :
    IsIso (C.normalizedOverlapMap C' D c i j hi hj) := by
  unfold normalizedOverlapMap
  infer_instance

/-- On affine tests, normalization recovers the effective affine comparison. -/
theorem normalizedOverlapMap_affine {A : CommRingCat.{u}} (c : Spec A ⟶ C.baseOverlap C')
    (i : Spec A ⟶ Spec C.baseRing) (j : Spec A ⟶ Spec C'.baseRing)
    (hi : c ≫ Limits.pullback.fst C.base C'.base = i)
    (hj : c ≫ Limits.pullback.snd C.base C'.base = j)
    (w : i ≫ C.base = j ≫ C'.base) :
    C.normalizedOverlapMap C' D c i j hi hj = (C.affineTestComparison C' i j w D).hom := by
  subst i j
  unfold normalizedOverlapMap SheafPullbackMapNormalization.normalize
  simp only [SheafPullbackPathComparison.comparison, pullbackCongr,
    eqToIso_refl, Iso.trans_refl]
  rw [C.baseOverlapComparison_normalize C' D c]
  simp only [Iso.inv_hom_id_app_assoc]

end FLT.Mazur.SchemeAffineDescent.Chart
