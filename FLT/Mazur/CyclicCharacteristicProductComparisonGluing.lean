/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductComparisonDiagram

/-!
# Gluing the full comparison scheme over the normalized product

The concrete affine comparison squares are cartesian. Relative gluing thus
constructs a scheme over the entire product, with the given affine charts
as its actual pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "X" => normalizedProduct n b c

/-- The full comparison projection is cartesian on every affine open inclusion. -/
theorem productComparisonProjection_equifibered :
    (productComparisonProjection n b c).Equifibered := by
  intro U V h
  exact (DirectedAffineSpectrum.isPullback_toOpen X (leOfHom h) _ _ _
    (affineComparisonOverlap_isPullback n b c
      (productOpenLeft n b c V) (productOpenRight n b c V)
      (productOpenLeft n b c U) (productOpenRight n b c U) _
      (productOpenLeft_refine n b c (leOfHom h))
      (productOpenRight_refine n b c (leOfHom h)))).flip

/-- The proven relative gluing datum of the full comparison schemes. -/
def productComparisonGluing : (X).directedAffineCover.RelativeGluingData where
  functor := productComparisonDiagram n b c
  natTrans := productComparisonProjection n b c
  equifibered := productComparisonProjection_equifibered n b c

/-- The full comparison scheme over the entire normalized chart product. -/
def productComparisonScheme : Scheme := (productComparisonGluing n b c).glued

/-- Its structure morphism to the actual normalized chart product. -/
def productComparisonStructure : productComparisonScheme n b c ⟶ X :=
  (productComparisonGluing n b c).toBase

/-- The original concrete comparison schemes cover the glued scheme. -/
def productComparisonCover : (productComparisonScheme n b c).OpenCover :=
  (productComparisonGluing n b c).cover

/-- Each original full comparison scheme is the actual preimage of its affine open. -/
theorem productComparisonChart_isPullback (U : (X).affineOpens) :
    IsPullback (productOpenComparisonStructure n b c U)
      ((productComparisonCover n b c).f U) U.1.ι (productComparisonStructure n b c) :=
  (productComparisonGluing n b c).isPullback_natTrans_ι_toBase U

/-- The glued comparison projection retains the original chart-product base maps. -/
@[reassoc] theorem productComparisonChart_structure (U : (X).affineOpens) :
    (productComparisonCover n b c).f U ≫ productComparisonStructure n b c =
      productOpenComparisonStructure n b c U ≫ U.1.ι :=
  (productComparisonGluing n b c).ι_toBase U

end FLT.Mazur.CyclicCharacteristicAtlas
