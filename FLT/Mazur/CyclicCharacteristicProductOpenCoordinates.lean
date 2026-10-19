/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductComparisonCharts
public import FLT.Mazur.DirectedAffineSpectrum

/-!
# Coordinates on every affine open of the normalized product

All affine opens give a locally directed cover, so overlaps of the original
product charts are included without choosing a common refinement.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "X" => normalizedProduct n b c

/-- The left endpoint of an affine open in the actual normalized product. -/
def productOpenLeft (U : (X).affineOpens) :
    Spec (DirectedAffineSpectrum.Ring X U) ⟶ normalizedLocus n b :=
  DirectedAffineSpectrum.chart X U ≫ prod.fst

/-- The right endpoint of the same affine open. -/
def productOpenRight (U : (X).affineOpens) :
    Spec (DirectedAffineSpectrum.Ring X U) ⟶ normalizedLocus n c :=
  DirectedAffineSpectrum.chart X U ≫ prod.snd

/-- Function restriction retains the actual left endpoint. -/
theorem productOpenLeft_refine {U V : (X).affineOpens} (h : U ≤ V) :
    productOpenLeft n b c U =
      Spec.map (CommRingCat.ofHom (DirectedAffineSpectrum.restriction X h)) ≫
        productOpenLeft n b c V :=
  (DirectedAffineSpectrum.restriction_chart_assoc X h prod.fst).symm

/-- Function restriction retains the actual right endpoint. -/
theorem productOpenRight_refine {U V : (X).affineOpens} (h : U ≤ V) :
    productOpenRight n b c U =
      Spec.map (CommRingCat.ofHom (DirectedAffineSpectrum.restriction X h)) ≫
        productOpenRight n b c V :=
  (DirectedAffineSpectrum.restriction_chart_assoc X h prod.snd).symm

end FLT.Mazur.CyclicCharacteristicAtlas
