/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCubicProjectiveCharts

/-!
# Scalars in a Laurent open chart

The structural coefficient map of a scheme over Spec K restricts to the
canonical constant Laurent polynomial under any torus open immersion over K.
-/

open CategoryTheory AlgebraicGeometry Opposite
open scoped LaurentPolynomial
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur
open ProjectiveLineMarkedSectionTransition PolygonCubicSections
variable (K : Type u) [Field K]

/-- Pulling constants along a morphism over K gives the torus structure scalars. -/
lemma torus_appTop_scalar {C : Over (Spec (.of K))}
    (f : MultiplicativeGroupScheme.gm K ⟶ C) (c : K) :
    f.left.appTop (C.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv c)) =
      laurentRing K (LaurentPolynomial.C c) := by
  have he := congrArg (fun g ↦ g.appTop) f.w
  rw [Scheme.Hom.comp_appTop] at he
  change C.hom.appTop ≫ f.left.appTop =
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : K →+* K[T;T⁻¹]))).appTop at he
  rw [← CommRingCat.comp_apply, he]
  exact (congrArg (fun g ↦ g.hom c) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (LaurentPolynomial.C : K →+* K[T;T⁻¹])))).symm

/-- The image-open coefficient map has exactly the constant Laurent coordinates. -/
lemma torus_image_scalar {C : Over (Spec (.of K))}
    (f : MultiplicativeGroupScheme.gm K ⟶ C) [IsOpenImmersion f.left] (c : K) :
    (f.left.appIso ⊤).hom (cubicOpenScalars K (f.left ''ᵁ ⊤) c) =
      laurentRing K (LaurentPolynomial.C c) := by
  change (f.left.appIso ⊤).hom (C.left.presheaf.map (homOfLE le_top).op
    (C.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) = _
  rw [Scheme.Hom.appIso_hom', ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  exact torus_appTop_scalar K f c

end FLT.Mazur
