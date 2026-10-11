/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineMonicComparison
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# The monic affine model inside the original projective cubic

The explicit coordinate algebra equivalence identifies the monic model with
chart two. Its inclusion into the glued cubic is an open immersion over the
original coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The monic affine model is the original chart with projective coordinate Z equal to one. -/
def monicChartIso : Spec (.of W.toAffine.CoordinateRing) ≅ chartScheme W 2 :=
  Scheme.Spec.mapIso (affineChartMonicEquiv W).toRingEquiv.toCommRingCatIso.op

/-- The monic affine model includes into the actual glued projective cubic. -/
def monicToIntegralCurve : Spec (.of W.toAffine.CoordinateRing) ⟶ integralCurve W :=
  (monicChartIso W).hom ≫ integralCurveChart W 2

/-- This inclusion is an open immersion. -/
instance monicToIntegralCurve_isOpenImmersion : IsOpenImmersion (monicToIntegralCurve W) := by
  unfold monicToIntegralCurve
  infer_instance

/-- The inclusion keeps the original coefficient map. -/
theorem monicToIntegralCurve_over :
    monicToIntegralCurve W ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing)) := by
  rw [monicToIntegralCurve, Category.assoc, integralCurveChart_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (affineChartMonicEquiv W).toAlgHom.comp_algebraMap

end FLT.Mazur.WeierstrassIntegralChart
