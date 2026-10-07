/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineChartDescent
public import FLT.Mazur.SchemeDescentCrossCoverCompatibility

/-!
# Effective comparison for two covering maps over one affine base

The original descent transport is compatible with the two actual affine data,
so effective affine descent constructs their comparison. Its reconstruction
square and faithful uniqueness retain the original cross-cover transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules} (D : Data p M)
variable (a : Spec R ⟶ X) (b c : Spec S ⟶ Y)
variable (wb : Spec.map φ ≫ a = b ≫ p) (wc : Spec.map φ ≫ a = c ≫ p)
variable (hφ : φ.hom.FaithfullyFlat)

/-- Transport between the covering maps intertwines the extracted affine data. -/
theorem affineChart_crossCover_compatible :
    AffineGeometricDescent.MapCompatible φ (D.affineChart φ p a b wb)
      (D.affineChart φ p a c wc) (D.transport b c (wb.symm.trans wc)).hom :=
  toAffine_mapCompatible φ (D.refine p (Spec.map φ) a b wb)
    (D.refine p (Spec.map φ) a c wc) _
    (D.transport_refine_compatible (Spec.map φ) a b c wb wc)

variable [((pullback b).obj M).IsQuasicoherent] [((pullback c).obj M).IsQuasicoherent]

/-- Effective affine descent constructs the comparison between unrelated covering maps. -/
def chartCrossCoverIso :
    D.chartSheaf φ p a b wb hφ ≅ D.chartSheaf φ p a c wc hφ :=
  AffineGeometricDescent.descendedIso φ (D.affineChart φ p a b wb)
    (D.affineChart φ p a c wc) hφ (D.transport b c (wb.symm.trans wc))
    (D.affineChart_crossCover_compatible φ p a b c wb wc)

/-- The descended cross-cover comparison reconstructs the original descent transport. -/
@[reassoc]
theorem chartCrossCoverIso_reconstruction :
    (pullback (Spec.map φ)).map (D.chartCrossCoverIso φ p a b c wb wc hφ).hom ≫
        (D.chartReconstruction φ p a c wc hφ).hom =
      (D.chartReconstruction φ p a b wb hφ).hom ≫
        (D.transport b c (wb.symm.trans wc)).hom :=
  AffineGeometricDescent.reconstruction_naturality φ (D.affineChart φ p a b wb)
    (D.affineChart φ p a c wc) (D.transport b c (wb.symm.trans wc)).hom
    (D.affineChart_crossCover_compatible φ p a b c wb wc) hφ

/-- The reconstruction square uniquely determines the effective cross-cover map. -/
theorem chartCrossCoverIso_unique
    (f : D.chartSheaf φ p a b wb hφ ⟶ D.chartSheaf φ p a c wc hφ)
    (hf : (pullback (Spec.map φ)).map f ≫ (D.chartReconstruction φ p a c wc hφ).hom =
      (D.chartReconstruction φ p a b wb hφ).hom ≫
        (D.transport b c (wb.symm.trans wc)).hom) :
    f = (D.chartCrossCoverIso φ p a b c wb wc hφ).hom :=
  AffineGeometricDescent.descendedMap_unique φ (D.affineChart φ p a b wb)
    (D.affineChart φ p a c wc) (D.transport b c (wb.symm.trans wc)).hom
    (D.affineChart_crossCover_compatible φ p a b c wb wc) hφ f hf

end FLT.Mazur.SchemeGeometricDescent.Data
