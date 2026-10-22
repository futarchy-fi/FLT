/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalPointAcyclic
public import FLT.Mazur.GenusOneGroupPointAcyclic
public import FLT.Mazur.SmoothGeneralizedCurveGroupIso
public import FLT.Mazur.GeneralizedCurveSmoothBaseDimension
public import FLT.Mazur.NodalFamilyGeometricConnected
public import FLT.Mazur.SmoothConnectedCurveGeometricIntegral

/-!
# Pole cohomology on every original geometric generalized curve

Classification separates smooth genus-one curves from arbitrary polygons.
Both branches compute the same actual smooth-marking coefficient. No equation,
pinching coordinates, integrality, or smoothness of the whole curve is input.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [IsAlgClosed K]
  (E : GeneralizedEllipticCurve (Spec (.of K)))
  (s : 𝟙_ (Over (Spec (.of K))) ⟶ E.group)

/-- Every positive smooth-marking power on the original geometric curve is acyclic. -/
theorem smoothMarkingPower_geometric_acyclic (m : ℕ) (hm : 0 < m) (r : ℕ) :
    Subsingleton (ModuleH (E.smoothMarkingPower s m) (r + 1)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  have hc := E.family.classified.fiber K (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
  rcases hc.classification with hsm | hpoly
  · let _ := hsm
    let _ := E.smooth_relativeDimension
    let _ := E.family.toNodalFamilyCore.fibers.geometricallyConnected
    let _ := smoothConnectedCurve_geometricallyIntegral E.curve.hom
    let _ := GeometricallyIntegral.isIntegral_of_subsingleton E.curve.hom
    let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
    have hf := E.family.genus.fiber K (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
    exact genusOne_group_pointPower_acyclic E.curve
      hf.toNodalFiberCore.topologicalKrullDim_eq_one hf.constantSections hf.genus_one
      (s ≫ E.inclusion) (E.smoothMarking_relativeCartier s).1 m hm r
  · exact PolygonOriginalPointPowers.acyclic_of_isNeronPolygon E hpoly s m hm r

/-- Every original positive smooth-marking pole space has dimension equal to its pole bound. -/
theorem smoothMarkingPower_geometric_h0 (m : ℕ) (hm : 0 < m) :
    Module.finrank K (ModuleScalarH E.curve.hom (E.smoothMarkingPower s m) 0) = m := by
  let _ : IsProper E.curve.hom := E.family.family.1
  have hc := E.family.classified.fiber K (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
  rcases hc.classification with hsm | hpoly
  · let _ := hsm
    let _ := E.smooth_relativeDimension
    let _ := E.family.toNodalFamilyCore.fibers.geometricallyConnected
    let _ := smoothConnectedCurve_geometricallyIntegral E.curve.hom
    let _ := GeometricallyIntegral.isIntegral_of_subsingleton E.curve.hom
    let _ : GrpObj E.curve := GrpObj.ofIso (asIso E.inclusion)
    have hf := E.family.genus.fiber K (𝟙 _) (𝟙 _) E.curve.hom IsPullback.of_id_fst
    exact genusOne_group_pointPower_h0 E.curve
      hf.toNodalFiberCore.topologicalKrullDim_eq_one hf.constantSections hf.genus_one
      (s ≫ E.inclusion) (E.smoothMarking_relativeCartier s).1 m hm
  · exact PolygonOriginalPointPowers.finrank_of_isNeronPolygon E hpoly s m hm

end FLT.Mazur.GeneralizedEllipticCurve
