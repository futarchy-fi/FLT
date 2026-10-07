/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeDescentAffineCharts
public import FLT.Mazur.AffineFiberProductMapCompatibility
public import FLT.Mazur.AffineGeometricDescentMorphisms

/-!
# Effective descent on actual affine charts of a scheme datum

Normalize compatible maps to affine tensor charts and descend the resulting
objects and maps. The local reconstruction square is the original scheme map
restricted to the cover chart. Assembly on open overlaps remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open AffineGeometricOverlap AffineOverlapTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable {M N : (Spec S).Modules} (D : Data (Spec.map φ) M) (E : Data (Spec.map φ) N)

/-- Affine normalization preserves the supplied scheme compatibility square. -/
theorem toAffine_mapCompatible (f : M ⟶ N) (hf : D.MapCompatible (Spec.map φ) E f) :
    AffineGeometricDescent.MapCompatible φ (D.toAffine φ) (E.toAffine φ) f := by
  let := φ.hom.toAlgebra
  change (fromFiberProduct R S M D.overlap).hom ≫ _ =
    _ ≫ (fromFiberProduct R S N E.overlap).hom
  exact fromFiberProduct_compatible R S D.overlap E.overlap f hf

variable {X Y : Scheme.{u}} (p : Y ⟶ X) {P Q : Y.Modules}
variable (F : Data p P) (G : Data p Q)
variable (a : Spec R ⟶ X) (b : Spec S ⟶ Y) (w : Spec.map φ ≫ a = b ≫ p)

/-- Restriction of a compatible scheme map intertwines the actual extracted affine data. -/
theorem affineChart_mapCompatible (f : P ⟶ Q) (hf : F.MapCompatible p G f) :
    AffineGeometricDescent.MapCompatible φ (F.affineChart φ p a b w)
      (G.affineChart φ p a b w) ((pullback b).map f) :=
  toAffine_mapCompatible φ (F.refine p (Spec.map φ) a b w)
    (G.refine p (Spec.map φ) a b w) ((pullback b).map f)
    (F.refine_mapCompatible p (Spec.map φ) a b w G f hf)

variable (hφ : φ.hom.FaithfullyFlat)
variable [((pullback b).obj P).IsQuasicoherent] [((pullback b).obj Q).IsQuasicoherent]

/-- The actual descended module sheaf of an affine chart of the scheme datum. -/
def chartSheaf : (Spec R).Modules :=
  AffineGeometricDescent.descendedSheaf φ ((pullback b).obj P)
    (F.affineChart φ p a b w) hφ

instance chartSheaf_isQuasicoherent : (F.chartSheaf φ p a b w hφ).IsQuasicoherent :=
  inferInstanceAs (AffineGeometricDescent.descendedSheaf φ _
    (F.affineChart φ p a b w) hφ).IsQuasicoherent

/-- Pullback reconstructs the original scheme sheaf on the chosen affine cover chart. -/
def chartReconstruction :
    (pullback (Spec.map φ)).obj (F.chartSheaf φ p a b w hφ) ≅ (pullback b).obj P :=
  AffineGeometricDescent.reconstruction φ _ (F.affineChart φ p a b w) hφ

variable (f : P ⟶ Q) (hf : F.MapCompatible p G f)

/-- Descend the actual restricted scheme map on the chosen affine chart. -/
def chartMap : F.chartSheaf φ p a b w hφ ⟶ G.chartSheaf φ p a b w hφ :=
  AffineGeometricDescent.descendedMap φ (F.affineChart φ p a b w)
    (G.affineChart φ p a b w) ((pullback b).map f)
    (affineChart_mapCompatible φ p F G a b w f hf) hφ

/-- The descended chart map reconstructs the original restricted scheme map. -/
@[reassoc]
theorem chartMap_reconstruction :
    (pullback (Spec.map φ)).map (chartMap φ p F G a b w hφ f hf) ≫
      (G.chartReconstruction φ p a b w hφ).hom =
    (F.chartReconstruction φ p a b w hφ).hom ≫ (pullback b).map f :=
  AffineGeometricDescent.reconstruction_naturality φ (F.affineChart φ p a b w)
    (G.affineChart φ p a b w) ((pullback b).map f)
    (affineChart_mapCompatible φ p F G a b w f hf) hφ

end FLT.Mazur.SchemeGeometricDescent.Data
