/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationAffineContraction
public import FLT.Mazur.WeierstrassModificationReesProjIso
public import FLT.Mazur.BlowupReesProper

/-!
# Properness over the original affine cubic

The proved Rees isomorphism preserves the actual affine coordinate
contraction, so this first whole local modification is proper over that
chart. Extending to the entire projective cubic requires exterior gluing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The actual Rees comparison preserves every original affine-cubic coordinate. -/
@[reassoc] theorem modificationProjIso_affineContraction :
    (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        BlowupRees.contraction (WeierstrassDilatation.modificationCenter W s) =
      WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6 := by
  apply (cancel_mono (WeierstrassIntegralChart.integralCurveChart W 2)).mp
  rw [Category.assoc, modificationProjIso_contraction,
    WeierstrassModificationX.affineContraction_toCurve]

include hs in
/-- The first equation modification is proper over its original affine cubic. -/
theorem affineContraction_isProper :
    IsProper (WeierstrassModificationX.affineContraction W s b3 b4 b6 h3 h4 h6) := by
  rw [← modificationProjIso_affineContraction W s b3 b4 b6 h3 h4 h6 hs]
  let _ := BlowupRees.contraction_isProper (WeierstrassDilatation.modificationCenter W s)
    (Submodule.fg_span (Set.toFinite _))
  infer_instance

end FLT.Mazur.WeierstrassModificationReesCoordinates
