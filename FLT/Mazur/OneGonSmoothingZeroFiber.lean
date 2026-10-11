/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingChartIntersection
public import FLT.Mazur.OneGonSmoothingFamily
public import FLT.Mazur.OneGonCocone
public import FLT.Mazur.SchemeOpenPushoutCoverIso

/-!
# The original pinched one-gon is the zero-parameter cubic

Glue the two explicit chart identifications along their original overlap.
The full-intersection and coverage proofs give a global isomorphism over K.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open PolygonNodePresentation OneGonTransition WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K]

/-- The actual original pinching is globally isomorphic to the zero-parameter family. -/
def zeroFiberIso : OneGonGluing.scheme K ≅ (family (0 : K)).left :=
  SchemeOpenPushout.coverIso (bPuncture K) (toTorus K)
    (zeroNodeInclusion K) (zeroTorusInclusion K) (zeroChart_isPullback K) (zeroCharts_cover K)

/-- The global comparison retains the original node chart with both its coordinates. -/
@[reassoc] theorem node_zeroFiberIso :
    OneGonGluing.node K ≫ (zeroFiberIso K).hom = zeroNodeInclusion K :=
  SchemeOpenPushout.inl_coverIso _ _ _ _ _ _

/-- The global comparison retains the original torus coordinate near the marking. -/
@[reassoc] theorem torus_zeroFiberIso :
    OneGonGluing.torus K ≫ (zeroFiberIso K).hom = zeroTorusInclusion K :=
  SchemeOpenPushout.inr_coverIso _ _ _ _ _ _

/-- The global comparison preserves the original coefficient structure morphism. -/
@[reassoc] theorem zeroFiberIso_structure :
    (zeroFiberIso K).hom ≫ (family (0 : K)).hom = OneGonGluing.toBase K := by
  apply pushout.hom_ext
  · change OneGonGluing.node K ≫ _ = OneGonGluing.node K ≫ _
    rw [node_zeroFiberIso_assoc, OneGonGluing.node_toBase]
    exact zeroNodeInclusion_structure K
  · change OneGonGluing.torus K ≫ _ = OneGonGluing.torus K ≫ _
    rw [torus_zeroFiberIso_assoc, OneGonGluing.torus_toBase]
    exact zeroTorusInclusion_structure K

/-- The inverse also preserves the original coefficient field. -/
@[reassoc] theorem zeroFiberIso_inv_structure :
    (zeroFiberIso K).inv ≫ OneGonGluing.toBase K = (family (0 : K)).hom := by
  rw [← zeroFiberIso_structure K, Iso.inv_hom_id_assoc]

/-- The isomorphism lies over the actual original base scheme. -/
def zeroFiberOverIso : OneGonNormalization.polygon K ≅ family (0 : K) :=
  Over.isoMk (zeroFiberIso K) (zeroFiberIso_structure K)

/-- The inverse recovers the actual original node inclusion. -/
@[reassoc] theorem zeroNodeInclusion_inverse :
    zeroNodeInclusion K ≫ (zeroFiberIso K).inv = OneGonGluing.node K := by
  rw [← node_zeroFiberIso K, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The inverse recovers the actual original torus inclusion. -/
@[reassoc] theorem zeroTorusInclusion_inverse :
    zeroTorusInclusion K ≫ (zeroFiberIso K).inv = OneGonGluing.torus K := by
  rw [← torus_zeroFiberIso K, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.OneGonSmoothing
