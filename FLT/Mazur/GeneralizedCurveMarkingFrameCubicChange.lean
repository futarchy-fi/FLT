/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingFrameAffineChange
public import FLT.Mazur.CartierComplementMorphismExt
public import FLT.Mazur.WeierstrassVariableChangeZero
public import FLT.Mazur.WeierstrassIntegralProper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Frame compatibility of the entire original cubic contraction

The explicit admissible change identifies the complete pointed cubics and
commutes with the original global maps. Schematic density extends the affine
identity across the marking, even for higher polygons and nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
  Scheme.Modules.pullback sectionPoleMultiplicativeCoordinates relativePoleFunction
variable {S : Scheme} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)
  (e f : (pullback (s ≫ E.inclusion).left).obj
    (divisorLineBundle (s ≫ E.inclusion).left.ker
      (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "W" => smoothMarkingWeierstrassCurve E s e
local notation "V" => smoothMarkingWeierstrassCurve E s f
local notation "C" => smoothMarkingFrameChange E s e f
local notation "hC" => smoothMarkingFrameChange_equation E s e f
local notation "U" => (TopologicalSpace.Closeds.compl (Scheme.IdealSheafData.support
  (Scheme.Hom.ker (Over.Hom.left (s ≫ E.inclusion)))) : E.curve.left.Opens)

/-- The complete cubic transition is the constructed admissible projective coordinate change. -/
def smoothMarkingFrameCubicIso : integralCurve (W) ≅ integralCurve (V) :=
  integralVariableChangeIso (V) (W) (C) (hC)

/-- The full transition preserves the original base spectrum. -/
@[reassoc] theorem smoothMarkingFrameCubicIso_over :
    (smoothMarkingFrameCubicIso E s e f).hom ≫ integralCurveStructure (V) =
      integralCurveStructure (W) := integralVariableChangeTo_structure (V) (W) (C) (hC)

/-- The full transition preserves the marked infinity section. -/
@[reassoc] theorem smoothMarkingFrameCubicIso_zero :
    integralCurveZero (W) ≫ (smoothMarkingFrameCubicIso E s e f).hom =
      integralCurveZero (V) := integralVariableChangeIso_zero (V) (W) (C) (hC)

/-- The full transition retains the exact original affine chart formula. -/
@[reassoc] theorem smoothMarkingFrameCubicIso_affine :
    integralCurveChart (W) 2 ≫ (smoothMarkingFrameCubicIso E s e f).hom =
      (affineVariableChangeIso (V) (W) (C) (hC)).hom ≫ integralCurveChart (V) 2 :=
  integralVariableChangeIso_affine (V) (W) (C) (hC)

/-- Changing the marking frame commutes with the entire original proper cubic morphism. -/
theorem smoothMarkingToIntegralCubic_frameChange :
    smoothMarkingToIntegralCubic E s e ≫ (smoothMarkingFrameCubicIso E s e f).hom =
      smoothMarkingToIntegralCubic E s f := by
  let _ : IsLocallyNoetherian S := isLocallyNoetherian_of_isOpenImmersion S.isoSpec.hom
  let _ : LocallyOfFinitePresentation E.curve.hom := E.family.family.2.2
  let _ : IsLocallyNoetherian E.curve.left :=
    LocallyOfFiniteType.isLocallyNoetherian E.curve.hom
  apply cartierComplement_hom_ext (smoothMarking_relativeCartier E s).1
    (integralCurveStructure (V))
  · rw [Category.assoc, smoothMarkingFrameCubicIso_over,
      smoothMarkingToIntegralCubic_over, smoothMarkingToIntegralCubic_over]
  · rw [← Category.assoc, ← smoothMarkingToIntegralAffineChart_cubic,
      Category.assoc, smoothMarkingFrameCubicIso_affine, ← Category.assoc,
      smoothMarkingToIntegralAffineChart_frameChange, smoothMarkingToIntegralAffineChart_cubic]

end FLT.Mazur.GeneralizedEllipticCurve
