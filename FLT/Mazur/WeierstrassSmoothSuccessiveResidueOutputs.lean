/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothSuccessiveResidueInputs

/-!
# The actual horizontal residue outputs on the successive chart

The output maps specialize the genuine integral horizontal action through
its common incidence refinement. Their coordinates retain the signed conic
parameter and the smooth character, including its inverse on the opposite branch.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationReesCoordinates WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (d : WeierstrassDividedDepth.Data W π (k + 1)) (hπ : π ≠ 0)
  (D : SplitNodeDepth W π depth) (hk0 : 0 < k + 1) (hk : 2 * (k + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => WeierstrassSuccessiveX.Coordinate W (π ^ k) π d.b3 d.b4 d.b6
local notation "t" => WeierstrassSuccessiveX.coord W (π ^ k) π d.b3 d.b4 d.b6 0
local notation "v" => WeierstrassSuccessiveX.coord W (π ^ k) π d.b3 d.b4 d.b6 1
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ k) π d.b3 d.b4 d.b6 2
local notation "t'" => WeierstrassModificationX.t W (π ^ k * π) d.b3 d.b4 d.b6
local notation "v'" => WeierstrassModificationX.v W (π ^ k * π) d.b3 d.b4 d.b6
local notation "a" => residue R W.a₁

local notation "τ" => smoothHorizontalTangentUnit D

/-- The first output obtained by specializing the original integral action transport. -/
def smoothSuccessiveFirstResidueOutput : A →ₐ[R] C :=
  (smoothSuccessiveFirstIntegralResidue d hπ D hk0 hk).comp
    (smoothSuccessiveIntegralOutput d hπ)

/-- The transported first output has the original smooth incidence character. -/
theorem smoothSuccessiveFirstResidueOutput_t :
    smoothSuccessiveFirstResidueOutput d hπ D hk0 hk t =
      (τ : C) * smoothHorizontalResidueConic D
        (LaurentPolynomial.C a * LaurentPolynomial.T 1) := by
  change smoothSuccessiveFirstIntegralResidue d hπ D hk0 hk
    (smoothSuccessiveIntegralOutput d hπ t) = _
  rw [← modificationMap_t W (π ^ k) π d.b3 d.b4 d.b6,
    smoothSuccessiveIntegralOutput_original, smoothSuccessiveFirstIntegralResidue_base]
  change smoothHorizontalFirstOutputResidue D d hk0 hk hπ
    (smoothHorizontalActionLift d (successiveHorizontalEquationMap d hπ t')) = _
  rw [successiveHorizontalEquationMap_t, smoothHorizontalFirstOutputResidue_scale]

/-- The original action output stays on the first slope branch. -/
theorem smoothSuccessiveFirstResidueOutput_v :
    smoothSuccessiveFirstResidueOutput d hπ D hk0 hk v = 0 := by
  change smoothSuccessiveFirstIntegralResidue d hπ D hk0 hk
    (smoothSuccessiveIntegralOutput d hπ v) = _
  rw [← modificationMap_v W (π ^ k) π d.b3 d.b4 d.b6,
    smoothSuccessiveIntegralOutput_original, smoothSuccessiveFirstIntegralResidue_base]
  change smoothHorizontalFirstOutputResidue D d hk0 hk hπ
    (smoothHorizontalActionLift d (successiveHorizontalEquationMap d hπ v')) = _
  rw [successiveHorizontalEquationMap_v]
  exact (smoothHorizontalFirstOutputResidue_action D d hk0 hk hπ).2

/-- The transported first output remains in the original incidence open. -/
theorem smoothSuccessiveFirstResidueOutput_unit :
    IsUnit (smoothSuccessiveFirstResidueOutput d hπ D hk0 hk t) := by
  rw [smoothSuccessiveFirstResidueOutput_t]
  exact (τ).isUnit.mul
    (smoothHorizontalConic_incidence_unit D)

/-- The first output's retained horizontal coordinate vanishes on the residue. -/
theorem smoothSuccessiveFirstResidueOutput_u :
    smoothSuccessiveFirstResidueOutput d hπ D hk0 hk u = 0 :=
  horizontal_zero_of_incidence_unit W (π ^ k) π d.b3 d.b4 d.b6 _
    (smoothSuccessiveFirstResidueOutput_unit d hπ D hk0 hk)
    (smoothHorizontalResidue_pi_zero D)

/-- The second output obtained by specializing the original integral action transport. -/
def smoothSuccessiveSecondResidueOutput : A →ₐ[R] C :=
  (smoothSuccessiveSecondIntegralResidue d hπ D hk0 hk).comp
    (smoothSuccessiveIntegralOutput d hπ)

/-- The transported second output has the original smooth incidence character. -/
theorem smoothSuccessiveSecondResidueOutput_t :
    smoothSuccessiveSecondResidueOutput d hπ D hk0 hk t =
      (↑τ⁻¹ : C) * smoothHorizontalResidueConic D
        (-LaurentPolynomial.C a * LaurentPolynomial.T 1) := by
  change smoothSuccessiveSecondIntegralResidue d hπ D hk0 hk
    (smoothSuccessiveIntegralOutput d hπ t) = _
  rw [← modificationMap_t W (π ^ k) π d.b3 d.b4 d.b6,
    smoothSuccessiveIntegralOutput_original, smoothSuccessiveSecondIntegralResidue_base]
  change smoothHorizontalSecondOutputResidue D d hk0 hk hπ
    (smoothHorizontalActionLift d (successiveHorizontalEquationMap d hπ t')) = _
  rw [successiveHorizontalEquationMap_t, smoothHorizontalSecondOutputResidue_scale]

/-- The original action output stays on the second slope branch. -/
theorem smoothSuccessiveSecondResidueOutput_v :
    smoothSuccessiveSecondResidueOutput d hπ D hk0 hk v = -algebraMap R C W.a₁ := by
  change smoothSuccessiveSecondIntegralResidue d hπ D hk0 hk
    (smoothSuccessiveIntegralOutput d hπ v) = _
  rw [← modificationMap_v W (π ^ k) π d.b3 d.b4 d.b6,
    smoothSuccessiveIntegralOutput_original, smoothSuccessiveSecondIntegralResidue_base]
  change smoothHorizontalSecondOutputResidue D d hk0 hk hπ
    (smoothHorizontalActionLift d (successiveHorizontalEquationMap d hπ v')) = _
  rw [successiveHorizontalEquationMap_v]
  exact (smoothHorizontalSecondOutputResidue_action D d hk0 hk hπ).2

/-- The transported second output remains in the original incidence open. -/
theorem smoothSuccessiveSecondResidueOutput_unit :
    IsUnit (smoothSuccessiveSecondResidueOutput d hπ D hk0 hk t) := by
  rw [smoothSuccessiveSecondResidueOutput_t]
  exact (τ⁻¹).isUnit.mul
    (smoothHorizontalConic_opposite_incidence_unit D)

/-- The second output's retained horizontal coordinate vanishes on the residue. -/
theorem smoothSuccessiveSecondResidueOutput_u :
    smoothSuccessiveSecondResidueOutput d hπ D hk0 hk u = 0 :=
  horizontal_zero_of_incidence_unit W (π ^ k) π d.b3 d.b4 d.b6 _
    (smoothSuccessiveSecondResidueOutput_unit d hπ D hk0 hk)
    (smoothHorizontalResidue_pi_zero D)

end FLT.Mazur.WeierstrassIntegralChart
