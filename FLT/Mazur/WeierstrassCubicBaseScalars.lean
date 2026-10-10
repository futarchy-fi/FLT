/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LocalizationDegreeFace
public import FLT.Mazur.ProjectiveAffineChartEmbedding
public import FLT.Mazur.WeierstrassSpecSections
public import FLT.Mazur.ScalarCohomology

/-!
# Compatibility of projective constants with the base projection

The constant sections used by the explicit cohomology computation are exactly
the scalars induced by the actual projection of the projective plane.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open FLT.Mazur.ProjectiveSpace FLT.Mazur.ProjectiveSpace.LocalizationDegree
open FLT.Mazur.FCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual plane projection induces the explicit constant-section scalar map. -/
theorem cubicPlane_specSectionHom (R : Type) [CommRing R] :
    specSectionHom (baseProjection R (Fin 3)) = constantSection R (Fin 3) ⊤ := by
  have ht : (Scheme.topIso (space R (Fin 3))).inv.appTop =
      (⊤ : (space R (Fin 3)).Opens).topIso.hom := by
    apply (cancel_epi (⊤ : (space R (Fin 3)).Opens).topIso.inv).mp
    rw [Iso.inv_hom_id]
    change (Scheme.topIso (space R (Fin 3))).hom.appTop ≫
      (Scheme.topIso (space R (Fin 3))).inv.appTop = _
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    rfl
  rw [baseProjection, specSectionHom_comp]
  ext r
  simp only [RingHom.comp_apply, specSectionHom, Proj.toSpecZero,
    Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rw [ht]
  simp only [Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp only [Scheme.isoOfEq_inv, Scheme.homOfLE_app, Scheme.Opens.topIso_inv,
    Scheme.Opens.topIso_hom]
  simp only [← Functor.map_comp_assoc]
  simp only [constantSection, RingHom.comp_apply, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom]
  rfl

/-- Over a field, the genus API's scalar map agrees with the Cech calculation's action. -/
theorem cubicPlane_structureScalarMap (K : Type) [Field K] :
    structureScalarMap (baseProjection K (Fin 3)) = constantSection K (Fin 3) ⊤ :=
  cubicPlane_specSectionHom K

end FLT.Mazur.WeierstrassIntegralChart
