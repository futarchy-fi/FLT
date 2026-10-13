/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSmoothStructureSheaf

/-!
# Affine-target rigidity over arbitrary original bases

The unrestricted proper smooth global-functions comparison makes evaluation
on a section faithful on maps to affine schemes. No Noetherian hypothesis on
the original base or a model of the original family is required.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
variable {X S Y : Scheme.{0}} (f : X ⟶ S)
  [IsProper f] [Smooth f] [GeometricallyConnected f]
  (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) [IsAffine Y]

include hs

/-- Pullback and section evaluation are inverse on the original global functions. -/
theorem properSmooth_section_appTop : s.appTop ≫ f.appTop = 𝟙 _ := by
  let _ : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr
    (ProperSmoothStructureSheaf.appTop_bijective f s hs)
  have h : f.appTop ≫ s.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
  apply (cancel_epi f.appTop).mp
  rw [← Category.assoc, h, Category.id_comp, Category.comp_id]

/-- Every affine-target map is constant along the original proper smooth fibers. -/
theorem properSmooth_to_affine_eq_section (a : X ⟶ Y) : a = f ≫ s ≫ a := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc,
    properSmooth_section_appTop f s hs, Category.comp_id]

/-- The original section detects equality without any condition on the base scheme. -/
theorem properSmooth_to_affine_ext (a b : X ⟶ Y) (hab : s ≫ a = s ≫ b) : a = b := by
  rw [properSmooth_to_affine_eq_section f s hs a,
    properSmooth_to_affine_eq_section f s hs b, hab]

end FLT.Mazur.FCurve
