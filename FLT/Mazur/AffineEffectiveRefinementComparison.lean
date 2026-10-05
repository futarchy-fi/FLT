/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDescentRefinementComparison
public import FLT.Mazur.AffineGeometricReconstructionCompatibility
public import FLT.Mazur.AffineRefinementCoactionCompatibility

/-!
# Effective comparison with the actual affine refinement

Restricting effective descent agrees with effective descent of the actual
refined geometric datum. Coaction compatibility is proved from the construction.
The comparison is uniquely determined by its geometric reconstruction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineDescentRefinement
open AffineGeometricDescent AffineGeometricDescentRecognition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S R' S' : CommRingCat.{u}}
variable (φ : R ⟶ S) (ψ : R' ⟶ S') (a : R ⟶ R') (b : S ⟶ S')
variable (w : φ ≫ b = a ≫ ψ) (hφ : φ.hom.FaithfullyFlat)
variable {M : (Spec S).Modules} [M.IsQuasicoherent] (D : Data φ M)
local instance : ((pullback (Spec.map b)).obj M).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback b M

/-- The actual restricted reconstruction is compatible with the actual refined datum. -/
theorem effective_reconstruction_compatible :
    CoactionCompatible ψ (sheaf φ a hφ D)
      (AffineGeometricOverlapRefinement.data φ ψ a b w M D)
      (reconstruction φ ψ a b w hφ D) :=
  refinement_compatible φ ψ a b w (descendedSheaf φ M D hφ) D
    (AffineGeometricDescent.reconstruction φ M D hφ) (reconstruction_compatible φ hφ D)

variable (hψ : ψ.hom.FaithfullyFlat)

/-- Restriction agrees with effective descent of the actual refined geometric datum. -/
def effectiveComparisonIso : sheaf φ a hφ D ≅
    descendedSheaf ψ ((pullback (Spec.map b)).obj M)
      (AffineGeometricOverlapRefinement.data φ ψ a b w M D) hψ :=
  comparisonIso φ ψ a b w hφ hψ D (AffineGeometricOverlapRefinement.data φ ψ a b w M D)
    (effective_reconstruction_compatible φ ψ a b w hφ D)

/-- The effective comparison has the actual restricted reconstruction. -/
@[reassoc]
theorem effectiveComparisonIso_reconstruction :
    (pullback (Spec.map ψ)).map (effectiveComparisonIso φ ψ a b w hφ D hψ).hom ≫
        (AffineGeometricDescent.reconstruction ψ ((pullback (Spec.map b)).obj M)
          (AffineGeometricOverlapRefinement.data φ ψ a b w M D) hψ).hom =
      (reconstruction φ ψ a b w hφ D).hom :=
  comparisonIso_reconstruction φ ψ a b w hφ hψ D _ _

/-- The reconstruction equation uniquely determines the effective comparison map. -/
theorem effectiveComparisonIso_unique
    (g : sheaf φ a hφ D ⟶ descendedSheaf ψ ((pullback (Spec.map b)).obj M)
      (AffineGeometricOverlapRefinement.data φ ψ a b w M D) hψ)
    (hg : (pullback (Spec.map ψ)).map g ≫
      (AffineGeometricDescent.reconstruction ψ ((pullback (Spec.map b)).obj M)
        (AffineGeometricOverlapRefinement.data φ ψ a b w M D) hψ).hom =
      (reconstruction φ ψ a b w hφ D).hom) :
    g = (effectiveComparisonIso φ ψ a b w hφ D hψ).hom :=
  sheafIso_unique ψ hψ (sheaf φ a hφ D) _ _
    (effective_reconstruction_compatible φ ψ a b w hφ D) g hg

end FLT.Mazur.AffineDescentRefinement
