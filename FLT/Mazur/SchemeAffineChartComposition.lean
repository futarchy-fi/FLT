/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapRefinementComposition
public import FLT.Mazur.SchemeAffineChartDescent
public import FLT.Mazur.SchemeAffineRefinementCompatibility

/-!
# Comparing affine chart data along successive scheme refinements

The cover composition chart identifies the affine refinement of an extracted
datum with the datum extracted directly from the composite scheme chart.
Effective descent then identifies their descended sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open AffineGeometricDescent AffineGeometricOverlapRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (α : R ⟶ R') (β : S ⟶ S')
variable (v : φ ≫ β = α ≫ ψ)
variable {X Y : Scheme.{u}} (p : Y ⟶ X) {M : Y.Modules} (D : Data p M)
variable (a : Spec R ⟶ X) (b : Spec S ⟶ Y) (w : Spec.map φ ≫ a = b ≫ p)

include w v in
/-- The composite affine chart square over the original scheme cover. -/
theorem affineChart_composite_square :
    Spec.map ψ ≫ (Spec.map α ≫ a) = (Spec.map β ≫ b) ≫ p :=
  SchemeOverlapRefinement.square_comp p (Spec.map φ) a b w (Spec.map ψ)
    (Spec.map α) (Spec.map β) (AffineRefinementPullback.spec_square φ ψ α β v)

/-- The cover composition chart intertwines the two actual extracted affine data. -/
theorem affineChart_refinementCompatible :
    AffineGeometricDescent.MapCompatible ψ
      (data φ ψ α β v ((pullback b).obj M) (D.affineChart φ p a b w))
      (D.affineChart ψ p (Spec.map α ≫ a) (Spec.map β ≫ b)
        (affineChart_composite_square φ ψ α β v p a b w))
      ((pullbackComp (Spec.map β) b).hom.app M) := by
  change AffineGeometricDescent.MapCompatible ψ
    (data φ ψ α β v _ ((D.refine p (Spec.map φ) a b w).toAffine φ)) _ _
  rw [← toAffine_refine]
  exact toAffine_mapCompatible ψ _ _ _
    (D.refine_composition_compatible p (Spec.map φ) a b w (Spec.map ψ)
      (Spec.map α) (Spec.map β) (AffineRefinementPullback.spec_square φ ψ α β v))

variable [((pullback b).obj M).IsQuasicoherent]
local instance : ((pullback (Spec.map β)).obj ((pullback b).obj M)).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback β _
/-- The composite cover chart remains quasi-coherent by the pullback composition iso. -/
instance isQuasicoherent_compositeChartPullback :
    ((pullback (Spec.map β ≫ b)).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec S').ringCatSheaf).prop_of_iso
    ((pullbackComp (Spec.map β) b).app M)
    (AffineModulePullbackSections.isQuasicoherent_pullback β ((pullback b).obj M))

variable (hψ : ψ.hom.FaithfullyFlat)

/-- Descend the actual composition chart between successive and direct affine chart data. -/
def affineChartCompositionIso :
    descendedSheaf ψ ((pullback (Spec.map β)).obj ((pullback b).obj M))
      (data φ ψ α β v ((pullback b).obj M) (D.affineChart φ p a b w)) hψ ≅
    D.chartSheaf ψ p (Spec.map α ≫ a) (Spec.map β ≫ b)
      (affineChart_composite_square φ ψ α β v p a b w) hψ :=
  descendedIso ψ _ _ hψ ((pullbackComp (Spec.map β) b).app M)
    (D.affineChart_refinementCompatible φ ψ α β v p a b w)

/-- The descended comparison reconstructs the specified cover composition chart. -/
@[reassoc]
theorem affineChartCompositionIso_reconstruction :
    (pullback (Spec.map ψ)).map (D.affineChartCompositionIso φ ψ α β v p a b w hψ).hom ≫
        (D.chartReconstruction ψ p (Spec.map α ≫ a) (Spec.map β ≫ b)
          (affineChart_composite_square φ ψ α β v p a b w) hψ).hom =
      (reconstruction ψ _
        (data φ ψ α β v ((pullback b).obj M) (D.affineChart φ p a b w)) hψ).hom ≫
          (pullbackComp (Spec.map β) b).hom.app M :=
  reconstruction_naturality ψ _ _ _
    (D.affineChart_refinementCompatible φ ψ α β v p a b w) hψ

end FLT.Mazur.SchemeGeometricDescent.Data
