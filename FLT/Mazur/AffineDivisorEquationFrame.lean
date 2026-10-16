/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePicardSectionCoordinates
public import FLT.Mazur.DivisorChartTensorNumerator
public import FLT.Mazur.ModuleSectionMap

/-!
# Affine divisor frames from the specified equation

The frame is reconstructed from evaluation on the supplied equation to its
original degree. Its action is exactly the original bounded numerator, so
no existential choice of a different Cartier generator enters the frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
variable {X : Scheme.{u}} [IsAffine X] {I : X.IdealSheafData} (hI : EffectiveCartier I)
variable (a : Γ(X, ⊤)) (ha : IsRegular a)
variable (he : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a})
local notation "U" => (Subtype.mk ⊤ (isAffineOpen_top X) : X.affineOpens)

/-- The degree-d frame uses precisely the supplied equation a to the power d. -/
irreducible_def divisorEquationPowerFrame (d : ℕ) :
    tensorPower (divisorLineBundle I hI) d ≅ structureModule X := by
  let _ := SchemePicard.rankOne_finitePresentation _
    (hI.pow d).divisorLineBundle_locallyFreeRankOne
  let _ := SchemePicard.rankOne_finitePresentation _
    (structureModule_locallyFreeRankOne (X := X))
  exact divisorLineBundlePowerIso hI d ≪≫ SchemePicard.isoOfSections
    (divisorNumerator (hI.pow d) (U) (a ^ d) (ha.pow d)
      (divisorChart_power_equation (U) a he d))

/-- The equation frame returns the same degree-bounded numerator on actual sections. -/
theorem divisorEquationPowerFrame_apply (d : ℕ)
    (s : Γ(tensorPower (divisorLineBundle I hI) d, ⊤)) :
    (divisorEquationPowerFrame hI a ha he d).hom.app ⊤ s =
      divisorChartTensorNumerator hI (U) a ha he d s := by
  let _ := SchemePicard.rankOne_finitePresentation _
    (hI.pow d).divisorLineBundle_locallyFreeRankOne
  let _ := SchemePicard.rankOne_finitePresentation _
    (structureModule_locallyFreeRankOne (X := X))
  rw [divisorEquationPowerFrame_def, sectionIso_trans,
    SchemePicard.isoOfSections_apply, divisorChartTensorNumerator_def]
  rfl

end FLT.Mazur.FCurve
