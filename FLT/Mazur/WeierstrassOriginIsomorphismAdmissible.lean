/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIsomorphismUnits
public import FLT.Mazur.WeierstrassTriangularAdmissible
public import FLT.Mazur.WeierstrassVariableChangeAffineRestriction
public import FLT.Mazur.WeierstrassAffineMorphismExt
public import FLT.Mazur.WeierstrassIntegralSeparated

/-!
# Every origin-preserving isomorphism is an admissible change

Recover the variable change from the actual coordinate pullback, then identify
its extension with the original isomorphism on the entire proper cubic.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

include hW in
/-- The actual coordinate pullback is an admissible change with the proved equation identity. -/
theorem originIsoCoordinateHom_exists_admissible : ∃ (C : VariableChange R) (h : C • V = W),
    originIsoCoordinateHom W V hV e hb hz = affineVariableChangeMap V W C h := by
  obtain ⟨r, t, v, s, w, hx, hy⟩ := originIsoCoordinateHom_exists_units W V hW hV e hb hz
  exact ⟨triangularVariableChange r t v s w,
    triangularVariableChange_curve W V _ r t v s w hx hy,
    triangularVariableChange_map W V _ r t v s w hx hy⟩

/-- Identifying the affine pullback identifies the original proper isomorphism. -/
theorem originIso_eq_integralVariableChange (C : VariableChange R) (h : C • V = W)
    (hf : originIsoCoordinateHom W V hV e hb hz = affineVariableChangeMap V W C h) :
    e = integralVariableChangeIso V W C h := by
  apply Iso.ext
  apply integralCurve_hom_ext_affine W (integralCurveStructure V)
  · exact hb.trans (integralVariableChangeTo_structure V W C h).symm
  · rw [integralVariableChangeIso_affine, ← originIsoAffineHom_inclusion W V hV e hb hz,
      ← originIsoCoordinateHom_spec W V hV e hb hz, hf]
    rfl

include hW hV hb hz in
/-- Any actual base- and origin-preserving isomorphism has an admissible global formula. -/
theorem originIso_exists_integralVariableChange : ∃ (C : VariableChange R) (h : C • V = W),
    e = integralVariableChangeIso V W C h := by
  obtain ⟨C, h, hf⟩ := originIsoCoordinateHom_exists_admissible W V hW hV e hb hz
  exact ⟨C, h, originIso_eq_integralVariableChange W V hV e hb hz C h hf⟩

end FLT.Mazur.WeierstrassIntegralChart
