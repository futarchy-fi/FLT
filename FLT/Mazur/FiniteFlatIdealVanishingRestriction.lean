/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatIdealVanishingChart
public import FLT.Mazur.AffinePreimageRestrictionPushout
public import FLT.Mazur.ProjectiveIdealVanishingRingPushout

/-!
# Restriction compatibility of finite flat vanishing charts

The coefficient ideal on a smaller affine open is exactly the restriction
of the coefficient ideal on the larger one. The proof uses the actual
cartesian family and preserves its complete ideal, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteFlatIdealVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D S : Scheme} (g : D ⟶ S) [IsFinite g] [Flat g]
  [LocallyOfFinitePresentation g] (J : D.IdealSheafData)

/-- The actual chart coefficient ideals commute with every affine open restriction. -/
theorem coefficientIdeal_map {U V : S.affineOpens} (h : V ≤ U) :
    (coefficientIdeal g J U).map (S.presheaf.map (homOfLE h).op).hom =
      coefficientIdeal g J V := by
  have H := ProjectiveIdealVanishing.ideal_ringPushout
    (S.presheaf.map (homOfLE h).op).hom (g.app U.1).hom (g.app V.1).hom
    (D.presheaf.map (homOfLE (g.preimage_mono h)).op).hom
    (AffinePreimageRestriction.sections_isPushout g h).flip
    (FCurve.finiteFlat_app_projective g U) (FCurve.finiteFlat_app_projective g V)
    (J.ideal ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩)
  dsimp only at H
  erw [J.map_ideal (U := ⟨g ⁻¹ᵁ V.1, V.2.preimage g⟩)
    (V := ⟨g ⁻¹ᵁ U.1, U.2.preimage g⟩) (g.preimage_mono h)] at H
  exact H.symm

/-- The chart equations form an actual ideal sheaf on the original base. -/
def idealSheaf : S.IdealSheafData where
  ideal := coefficientIdeal g J
  map_ideal_basicOpen U f := coefficientIdeal_map g J (S.affineBasicOpen_le f)

/-- The global ideal sheaf has exactly the original chart ideal on every affine open. -/
theorem idealSheaf_ideal (U : S.affineOpens) :
    (idealSheaf g J).ideal U = coefficientIdeal g J U := rfl

/-- The global closed locus obtained by gluing the coefficient charts. -/
def locus : Scheme := (idealSheaf g J).subscheme

/-- Its original closed immersion into the parameter base. -/
def locusInclusion : locus g J ⟶ S := (idealSheaf g J).subschemeι

instance locusInclusion_closed : IsClosedImmersion (locusInclusion g J) :=
  inferInstanceAs (IsClosedImmersion (idealSheaf g J).subschemeι)

end FLT.Mazur.FiniteFlatIdealVanishing
