/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEffectiveRefinementComparison
public import FLT.Mazur.AffineRefinedCompositionCompatibility

/-!
# Descending the affine cover composition chart

The actual cover composition chart identifies successive refinement data with
composite refinement data. Effective descent carries it to an isomorphism,
whose reconstruction is the original cover chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDescentRefinement
open AffineGeometricDescent AffineGeometricDescentRecognition
open AffineGeometricOverlapRefinement AffineRefinementPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' R'' S'' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (χ : R'' ⟶ S'')
variable (a : R ⟶ R') (b : S ⟶ S') (c : R' ⟶ R'') (d : S' ⟶ S'')
variable (w : φ ≫ b = a ≫ ψ) (v : ψ ≫ d = c ≫ χ)
variable (hφ : φ.hom.FaithfullyFlat)
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)
local instance isQuasicoherent_compositionChartPullback {T U : CommRingCat.{u}} (f : T ⟶ U)
    (P : (Spec T).Modules) [P.IsQuasicoherent] :
    ((pullback (Spec.map f)).obj P).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback f P

include hφ in
/-- The cover composition chart intertwines the actual effectively refinable data. -/
theorem effectiveCompositionData_compatible :
    MapCompatible χ
      (data ψ χ c d v ((pullback (Spec.map b)).obj M) (data φ ψ a b w M D))
      (data φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v) M D)
      (compositionChart b d M).hom :=
  compositionData_compatible φ ψ χ a b c d w v D
    (AffineGeometricDescent.reconstruction φ M D hφ) (reconstruction_compatible φ hφ D)

variable (hχ : χ.hom.FaithfullyFlat)

/-- Descent of the actual cover composition chart. -/
def compositionDescentIso :
    descendedSheaf χ ((pullback (Spec.map d)).obj ((pullback (Spec.map b)).obj M))
      (data ψ χ c d v ((pullback (Spec.map b)).obj M) (data φ ψ a b w M D)) hχ ≅
    descendedSheaf χ ((pullback (Spec.map (b ≫ d))).obj M)
      (data φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v) M D) hχ :=
  descendedIso χ _ _ hχ (compositionChart b d M)
    (effectiveCompositionData_compatible φ ψ χ a b c d w v hφ D)

/-- The descended composition chart reconstructs the actual cover chart. -/
@[reassoc]
theorem compositionDescentIso_reconstruction :
    (pullback (Spec.map χ)).map (compositionDescentIso φ ψ χ a b c d w v hφ D hχ).hom ≫
        (AffineGeometricDescent.reconstruction χ _
          (data φ χ (a ≫ c) (b ≫ d) (composite_square φ ψ χ a b c d w v) M D) hχ).hom =
      (AffineGeometricDescent.reconstruction χ _
        (data ψ χ c d v ((pullback (Spec.map b)).obj M) (data φ ψ a b w M D)) hχ).hom ≫
          (compositionChart b d M).hom :=
  AffineGeometricDescent.reconstruction_naturality χ _ _ _
    (effectiveCompositionData_compatible φ ψ χ a b c d w v hφ D) hχ

end FLT.Mazur.AffineDescentRefinement
