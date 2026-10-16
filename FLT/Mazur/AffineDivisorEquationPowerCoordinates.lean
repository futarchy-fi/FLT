/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineDivisorEquationFrameTransport
public import FLT.Mazur.ModuleFrameRegularCoordinates
public import FLT.Mazur.SectionGradedCoordinates

/-!
# Degree coherence of the specified affine equation frames

Construct the line frame by evaluation on the specified regular equation.
Its tensor-power coordinates equal the original degree-wise equation
coordinates, since both preserve the same regular canonical section.
Consequently these original coordinates multiply across degrees.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor
variable {X : Scheme} [IsAffine X] {I : X.IdealSheafData} (hI : EffectiveCartier I)
variable (a : Γ(X, ⊤)) (ha : IsRegular a)
variable (he : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {a})
local notation "L" => divisorLineBundle I hI

/-- The line frame evaluates on the original equation, without a generator choice. -/
irreducible_def divisorEquationLineFrame : (L) ≅ structureModule X := by
  let _ := SchemePicard.rankOne_finitePresentation _ hI.divisorLineBundle_locallyFreeRankOne
  let _ := SchemePicard.rankOne_finitePresentation _
    (structureModule_locallyFreeRankOne (X := X))
  exact SchemePicard.isoOfSections
    (divisorNumerator hI ⟨⊤, isAffineOpen_top X⟩ a ha he)

/-- The reconstructed line frame is exactly the specified equation numerator. -/
theorem divisorEquationLineFrame_apply (s : Γ((L), ⊤)) :
    (divisorEquationLineFrame hI a ha he).hom.app ⊤ s =
      divisorNumerator hI ⟨⊤, isAffineOpen_top X⟩ a ha he s := by
  let _ := SchemePicard.rankOne_finitePresentation _ hI.divisorLineBundle_locallyFreeRankOne
  let _ := SchemePicard.rankOne_finitePresentation _
    (structureModule_locallyFreeRankOne (X := X))
  rw [divisorEquationLineFrame_def, SchemePicard.isoOfSections_apply]
  rfl

/-- The canonical line section has precisely the original regular equation as coordinate. -/
theorem divisorEquationLineFrame_canonical :
    (divisorEquationLineFrame hI a ha he).hom.app ⊤ (divisorSection hI ⊤) = a := by
  rw [divisorEquationLineFrame_apply, divisorNumerator_apply, divisorSection_eval]
  change 1 * a = a
  exact one_mul _

/-- All existing degree-wise equation coordinates are powers of the same original line frame. -/
theorem divisorEquationPowerFrame_tensor (d : ℕ) (s : Γ(tensorPower (L) d, ⊤)) :
    (divisorEquationPowerFrame hI a ha he d).hom.app ⊤ s =
      (tensorPowerTrivialization (divisorEquationLineFrame hI a ha he) d).hom.app ⊤ s := by
  apply frame_apply_eq_of_regular _ _ ⊤
    (tensorPowerSection (L) ⊤ (divisorSection hI ⊤) d)
  · rw [tensorPowerTrivialization_section, divisorEquationLineFrame_canonical]
    exact ha.pow d
  · rw [divisorEquationPowerFrame_canonical, tensorPowerTrivialization_section,
      divisorEquationLineFrame_canonical]

/-- Original equation coordinates multiply under the genuine section-ring multiplication. -/
theorem divisorEquationPowerFrame_mul (d e : ℕ)
    (s : Γ(tensorPower (L) d, ⊤)) (v : Γ(tensorPower (L) e, ⊤)) :
    (divisorEquationPowerFrame hI a ha he (d + e)).hom.app ⊤
      (SectionGradedMultiplication.mul (L) ⊤ d e s v) =
        (show Γ(X, ⊤) from (divisorEquationPowerFrame hI a ha he d).hom.app ⊤ s) *
          (show Γ(X, ⊤) from (divisorEquationPowerFrame hI a ha he e).hom.app ⊤ v) := by
  simp only [divisorEquationPowerFrame_tensor]
  exact SectionGradedCoordinates.coordinate_mul (divisorEquationLineFrame hI a ha he) d e ⊤ s v

end FLT.Mazur.FCurve
