/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEffectiveRefinementNaturality
public import FLT.Mazur.AffineRefinementIdentity

/-!
# Identity coherence for effective affine refinement

The unit chart intertwines the actual identity-refined datum and the original
datum. After descending this chart, effective comparison is the base unit chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDescentRefinement
open AffineGeometricDescent AffineGeometricDescentRecognition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
variable (a : R ⟶ R) (b : S ⟶ S) (w : φ ≫ b = a ≫ φ)
variable (ha : Spec.map a = 𝟙 (Spec R)) (hb : Spec.map b = 𝟙 (Spec S))
variable (hφ : φ.hom.FaithfullyFlat)
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)
local instance : ((pullback (Spec.map b)).obj M).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback b M

include hφ ha in
/-- The unit chart identifies the actual datum refined along identity scheme maps. -/
theorem identityData_compatible :
    MapCompatible φ (AffineGeometricOverlapRefinement.data φ φ a b w M D) D
      (SchemePullbackSquare.identityChart (Spec.map b) hb M).hom :=
  mapCompatible_of_reconstruction φ _ D (reconstruction φ φ a b w hφ D)
    (AffineGeometricDescent.reconstruction φ M D hφ)
    (effective_reconstruction_compatible φ φ a b w hφ D)
    (reconstruction_compatible φ hφ D)
    (SchemePullbackSquare.identityChart (Spec.map a) ha (descendedSheaf φ M D hφ)).hom _
    (AffineRefinementPullback.reconstruction_identity φ a b ha hb w
      (AffineGeometricDescent.reconstruction φ M D hφ)).symm

/-- Descent of the actual cover unit chart identifies the two descended sheaves. -/
def identityDescentIso :
    descendedSheaf φ ((pullback (Spec.map b)).obj M)
      (AffineGeometricOverlapRefinement.data φ φ a b w M D) hφ ≅
      descendedSheaf φ M D hφ :=
  descendedIso φ _ D hφ (SchemePullbackSquare.identityChart (Spec.map b) hb M)
    (identityData_compatible φ a b w ha hb hφ D)

/-- Effective refinement along identity scheme maps agrees with the actual base unit chart. -/
@[reassoc]
theorem effectiveComparisonIso_identity :
    (effectiveComparisonIso φ φ a b w hφ D hφ).hom ≫
        (identityDescentIso φ a b w ha hb hφ D).hom =
      (SchemePullbackSquare.identityChart (Spec.map a) ha (descendedSheaf φ M D hφ)).hom := by
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique φ hφ
    (AffineGeometricDescent.reconstruction φ M D hφ)
  rw [Functor.map_comp, Category.assoc]
  change (pullback (Spec.map φ)).map (effectiveComparisonIso φ φ a b w hφ D hφ).hom ≫
      (pullback (Spec.map φ)).map
        (descendedMap φ _ D _ (identityData_compatible φ a b w ha hb hφ D) hφ) ≫ _ = _
  rw [AffineGeometricDescent.reconstruction_naturality, ← Category.assoc,
    effectiveComparisonIso_reconstruction]
  exact AffineRefinementPullback.reconstruction_identity φ a b ha hb w
    (AffineGeometricDescent.reconstruction φ M D hφ)

end FLT.Mazur.AffineDescentRefinement
