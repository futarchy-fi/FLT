/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingMarkedCoordinates
public import FLT.Mazur.SectionPoleCanonicalCoefficient
public import FLT.Mazur.GeneralizedCurveMarkingCubicFactorization

/-!
# The actual standard-chart preimages of the relative cubic map

The integral cubic factorization has the same generator opens as the original
projective presentation. Its Z chart is the marking complement, while its Y
chart contains the entire original marking over the varying base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle sectionPoleMultiplicativeCoordinates
  Scheme.Modules.pullback ModuleSheafTensor.tensor

variable {S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (E : GeneralizedEllipticCurve S) (s : 𝟙_ (Over S) ⟶ E.group)

local notation "t" => s ≫ E.inclusion
local notation "hI" => And.left (smoothMarking_relativeCartier E s)

local instance generalizedCurveMarkingCubicPreimagesProper :
    IsProper E.curve.hom := E.family.family.1

variable (e : (pullback (s ≫ E.inclusion).left).obj
  (divisorLineBundle (s ≫ E.inclusion).left.ker
    (smoothMarking_relativeCartier E s).1) ≅ structureModule S)

local notation "L" => divisorLineBundle (Scheme.Hom.ker (Over.Hom.left (t))) (hI)
local notation "T" => smoothMarkingProjectiveSections E s e
local notation "W" => smoothMarkingWeierstrassCurve E s e
open WeierstrassIntegralChart

/-- Each integral chart pulls back to the actual original generator open. -/
theorem smoothMarkingToIntegralCubic_preimage_chart (j : Fin 3) :
    smoothMarkingToIntegralCubic E s e ⁻¹ᵁ (integralCurveChart (W) j).opensRange =
      sectionGeneratorOpen (tensorPower (L) 3) (T j) := by
  rw [← integralProjectiveMap_preimage_chart, ← Scheme.Hom.comp_preimage,
    smoothMarkingToIntegralCubic_projective, smoothMarkingToProjectiveSpace,
    sectionProjectiveMorphism_preimage_chart]

/-- The affine cubic chart has exactly the original marked-point complement as preimage. -/
theorem smoothMarkingToIntegralCubic_preimage_z :
    smoothMarkingToIntegralCubic E s e ⁻¹ᵁ (integralCurveChart (W) 2).opensRange =
      (t).left.ker.support.compl := by
  rw [← integralProjectiveMap_preimage_chart, ← Scheme.Hom.comp_preimage,
    smoothMarkingToIntegralCubic_projective, smoothMarkingToProjectiveSpace_preimage_z]

/-- Along the original marking the Y generator open is the whole base. -/
theorem smoothMarkingMarking_preimage_yGenerator :
    (t).left ⁻¹ᵁ sectionGeneratorOpen (tensorPower (L) 3) (T 1) = ⊤ := by
  rw [← sectionPoleCoefficient_basicOpen (t).left (hI) e 3,
    smoothMarkingProjectiveSections_coefficient, Matrix.cons_val_one,
    Matrix.cons_val_zero, Scheme.basicOpen_one]

/-- The marking lands in the actual integral Y chart, including over nonreduced bases. -/
theorem smoothMarkingMarking_preimage_y :
    ((t).left ≫ smoothMarkingToIntegralCubic E s e) ⁻¹ᵁ
      (integralCurveChart (W) 1).opensRange = ⊤ := by
  rw [Scheme.Hom.comp_preimage, smoothMarkingToIntegralCubic_preimage_chart,
    smoothMarkingMarking_preimage_yGenerator]

end FLT.Mazur.GeneralizedEllipticCurve
