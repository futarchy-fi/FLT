/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCanonicalMapCompatibility
public import FLT.Mazur.AffineEffectiveRefinementComparison

/-!
# Naturality of effective affine refinement

Restriction preserves compatibility with the actual refined data. The effective
descent comparisons therefore commute with every compatible original map,
without a separate assumption about the refined map.
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
variable {M N : (Spec S).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
local instance (P : (Spec S).Modules) [P.IsQuasicoherent] :
    ((pullback (Spec.map b)).obj P).IsQuasicoherent :=
  AffineModulePullbackSections.isQuasicoherent_pullback b P
variable (D : Data φ M) (E : Data φ N) (f : M ⟶ N) (hf : MapCompatible φ D E f)

include hφ hf in
/-- Restriction of a compatible map intertwines the actual refined geometric data. -/
theorem refinedMap_compatible :
    MapCompatible ψ (AffineGeometricOverlapRefinement.data φ ψ a b w M D)
      (AffineGeometricOverlapRefinement.data φ ψ a b w N E) ((pullback (Spec.map b)).map f) :=
  mapCompatible_of_reconstruction ψ _ _ (reconstruction φ ψ a b w hφ D)
    (reconstruction φ ψ a b w hφ E) (effective_reconstruction_compatible φ ψ a b w hφ D)
    (effective_reconstruction_compatible φ ψ a b w hφ E) (map φ a hφ D E f hf) _
    (reconstruction_naturality φ ψ a b w hφ D E f hf)

/-- Effective refinement comparisons are natural for every compatible original map. -/
@[reassoc]
theorem effectiveComparisonIso_naturality (hψ : ψ.hom.FaithfullyFlat) :
    (effectiveComparisonIso φ ψ a b w hφ D hψ).hom ≫
        descendedMap ψ (AffineGeometricOverlapRefinement.data φ ψ a b w M D)
          (AffineGeometricOverlapRefinement.data φ ψ a b w N E)
          ((pullback (Spec.map b)).map f) (refinedMap_compatible φ ψ a b w hφ D E f hf) hψ =
      map φ a hφ D E f hf ≫ (effectiveComparisonIso φ ψ a b w hφ E hψ).hom :=
  comparisonIso_naturality φ ψ a b w hφ hψ D _
    (effective_reconstruction_compatible φ ψ a b w hφ D) E _
    (effective_reconstruction_compatible φ ψ a b w hφ E) f hf
    (refinedMap_compatible φ ψ a b w hφ D E f hf)

end FLT.Mazur.AffineDescentRefinement
