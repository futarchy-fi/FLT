/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativePushforwardOpens
public import FLT.Mazur.IdealAdicRelativeChartScalar

/-!
# Original scalars in the geometric tensor charts

The actual map from each tensor chart to the original scheme is induced
by the original chart scalar ring homomorphism, including the closed quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

omit [IsLocallyNoetherian Y] in
/-- The closed affine chart map is induced by the actual quotient of structure sections. -/
lemma closedAffineChart_toSource (U : X.affineOpens) :
    (closedAffineChart J f U).2.fromSpec ≫ (J.comap f).subschemeι =
      Spec.map ((J.comap f).subschemeι.app U.1) ≫ U.2.fromSpec := by
  rw [Scheme.Hom.app_eq_appLE]
  exact
    (IsAffineOpen.SpecMap_appLE_fromSpec (J.comap f).subschemeι
      U.2 (closedAffineChart J f U).2 le_rfl).symm

/-- The actual tensor chart to the original source is the spectrum of its chart scalar map. -/
lemma relativeTensorChart_toSource (U : X.affineOpens) :
    let := closedBaseAlgebra J f U.1
    relativeTensorChart J f U ≫ relativeSchemeToSource J f =
      Spec.map (CommRingCat.ofHom (relativeChartScalar J f U)) ≫ U.2.fromSpec := by
  let := closedBaseAlgebra J f U.1
  dsimp only
  unfold relativeSchemeToSource
  rw [relativeTensorChart_toClosed_assoc, closedAffineChart_toSource, ← Category.assoc]
  unfold relativeTensorToChart
  rw [← Spec.map_comp]
  rfl

/-- The source chart pulls back to the whole tensor spectrum. -/
lemma relativeTensorChart_source_preimage (U : X.affineOpens) :
    (relativeTensorChart J f U ≫ relativeSchemeToSource J f) ⁻¹ᵁ U.1 = ⊤ := by
  rw [relativeTensorChart_toSource, Scheme.Hom.comp_preimage,
    U.2.fromSpec_preimage_self, Scheme.Hom.preimage_top]

/-- The actual chart projection pulls structure scalars back by the original scalar map. -/
lemma relativeTensorChart_source_scalar (U : X.affineOpens) :
    (relativeTensorChart J f U ≫ relativeSchemeToSource J f).appLE U.1 ⊤
        (relativeTensorChart_source_preimage J f U).ge =
      CommRingCat.ofHom (relativeChartScalar J f U) ≫
        (Scheme.ΓSpecIso (.of (RelativeAlgebra J f U))).inv := by
  let := closedBaseAlgebra J f U.1
  have h : U.2.fromSpec.appLE U.1 ⊤ U.2.fromSpec_preimage_self.ge =
      (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
    simp only [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc,
      ← Functor.map_comp, ← op_comp, homOfLE_comp_eqToHom, homOfLE_refl,
      op_id]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [relativeTensorChart_toSource]
  rw [← Scheme.Hom.appLE_comp_appLE
    (Spec.map (CommRingCat.ofHom (relativeChartScalar J f U))) U.2.fromSpec
    U.1 ⊤ ⊤ U.2.fromSpec_preimage_self.ge (by simp)]
  rw [h]
  erw [Scheme.Hom.appLE_eq_app]
  change (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫
    (Spec.map (CommRingCat.ofHom (relativeChartScalar J f U))).appTop = _
  exact (Scheme.ΓSpecIso_inv_naturality _).symm

end FLT.Mazur.IdealAdicGradedPullback
