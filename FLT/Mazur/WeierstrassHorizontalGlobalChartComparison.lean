/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationFractionCover

/-!
# The horizontal global fraction input is the original equation chart

The comparison follows the actual glued Rees isomorphism, retaining the
horizontal algebra equivalence and the equation chart embedding. It applies
on the entire chart, before restricting to either residue conic branch.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationReesCoordinates
open WeierstrassIntegralChart WeierstrassGlobalModification
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
local notation "e" => modificationProjIso W s b3 b4 b6 h3 h4 h6 hs
local notation "E" => WeierstrassModificationX.horizontalReesChartEquiv W s b3 b4 b6
  h3 h4 h6 hs

/-- The actual inverse Rees comparison retains the full original horizontal chart. -/
@[reassoc] theorem horizontalProjInclusion_modificationProjIso_inv :
    horizontalProjInclusion W s ≫ (e).inv =
      (horizontalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationX.xChart W s b3 b4 b6 := by
  apply (cancel_mono (e).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = ((horizontalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
    WeierstrassModificationX.xChart W s b3 b4 b6) ≫
      modificationToProj W s b3 b4 b6 h3 h4 h6 hs
  rw [← horizontalChart_atlasIso, Category.assoc, fractionAtlasIso_toProj,
    horizontalChart_toProj]

/-- The full global horizontal fraction map is the original equation chart inclusion. -/
theorem originalHorizontalFractionCoverMap_eq :
    originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs (some 1) =
      (horizontalChartIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
        WeierstrassModificationX.xChart W s b3 b4 b6 ≫
          localChart W s b3 b4 b6 h3 h4 h6 hs := by
  have h := horizontalProjInclusion_modificationProjIso_inv_assoc W s b3 b4 b6
    h3 h4 h6 hs (localChart W s b3 b4 b6 h3 h4 h6 hs)
  convert h using 1 <;> rfl

/-- The chart comparison uses the spectrum of the original horizontal algebra equivalence. -/
theorem originalHorizontalFractionCoverMap_spec :
    originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs (some 1) =
      Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom E).toRingHom) ≫
        WeierstrassModificationX.xChart W s b3 b4 b6 ≫
          localChart W s b3 b4 b6 h3 h4 h6 hs := by
  rw [originalHorizontalFractionCoverMap_eq]
  rfl

end FLT.Mazur.WeierstrassModificationReesCoordinates
