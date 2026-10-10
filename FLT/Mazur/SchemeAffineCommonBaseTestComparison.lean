/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSchemeTestComparison

/-!
# Effective comparisons in specified common-base ring coordinates

The glued scheme-test comparison at two spectrum maps is exactly the
effective comparison on the constructed common faithfully flat cover.
This makes its reconstruction equation available without coordinate casts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {A : CommRingCat.{u}} (f : C.baseRing ⟶ A) (g : C'.baseRing ⟶ A)
variable (w : Spec.map f ≫ C.base = Spec.map g ≫ C'.base)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
attribute [local irreducible] sheaf CrossRefinement.effectiveComparison

private lemma effectiveComparison_coordinates
    (f' : C.baseRing ⟶ A) (g' : C'.baseRing ⟶ A)
    (hf : f' = f) (hg : g' = g)
    (hf' : Spec.map f' = Spec.map f) (hg' : Spec.map g' = Spec.map g)
    (w' : Spec.map f' ≫ C.base = Spec.map g' ≫ C'.base) :
    (((pullbackCongr hf').app (C.sheaf D)).symm ≪≫
        (C.commonBaseCrossRefinement C' f' g' w').effectiveComparison D ≪≫
        (pullbackCongr hg').app (C'.sheaf D)).hom =
      ((C.commonBaseCrossRefinement C' f g w).effectiveComparison D).hom := by
  subst f' g'
  change (𝟙 _ ≫ ((C.commonBaseCrossRefinement C' f g w).effectiveComparison D).hom ≫
    𝟙 _) = _
  rw [Category.comp_id, Category.id_comp]

/-- The scheme test on specified spectrum maps retains its common-cover comparison. -/
lemma schemeTestComparison_commonBase :
    C.schemeTestComparison C' D (Spec.map f) (Spec.map g) w =
      ((C.commonBaseCrossRefinement C' f g w).effectiveComparison D).hom := by
  rw [schemeTestComparison_affine]
  exact effectiveComparison_coordinates C C' f g w D
    (Spec.preimage (Spec.map f)) (Spec.preimage (Spec.map g))
    (Spec.preimage_map f) (Spec.preimage_map g) _ _ _

end FLT.Mazur.SchemeAffineDescent.Chart
