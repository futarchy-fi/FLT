/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothSuccessiveIntegralTransport
public import FLT.Mazur.WeierstrassSuccessiveXIncidenceExt

/-!
# The original residue inputs after integral successive-chart transport

Both branch maps are obtained from the common integral refinement. Their
three coordinates retain the independent conic parameter, the original
slope, and the vanishing horizontal coordinate.
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

omit [IsDomain R] in
/-- The uniformizer vanishes in the original independent residue product. -/
theorem smoothHorizontalResidue_pi_zero : algebraMap R C π = 0 := by
  rw [IsScalarTower.algebraMap_apply R K C, ResidueField.algebraMap_eq,
    (residue_eq_zero_iff π).mpr (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π),
    map_zero]

/-- The first input obtained by specializing the actual integral transport. -/
def smoothSuccessiveFirstResidueInput : A →ₐ[R] C :=
  (smoothSuccessiveFirstIntegralResidue d hπ D hk0 hk).comp
    (smoothSuccessiveIntegralInput d hπ)

/-- The transported first incidence retains its original signed conic coordinate. -/
theorem smoothSuccessiveFirstResidueInput_t :
    smoothSuccessiveFirstResidueInput d hπ D hk0 hk t =
      smoothHorizontalResidueConic D (LaurentPolynomial.C a * LaurentPolynomial.T 1) := by
  change smoothSuccessiveFirstIntegralResidue d hπ D hk0 hk
    (smoothSuccessiveIntegralInput d hπ t) = _
  rw [← modificationMap_t W (π ^ k) π d.b3 d.b4 d.b6,
    smoothSuccessiveIntegralInput_original, smoothSuccessiveFirstIntegralResidue_base]
  change smoothHorizontalIntegralFirstResidue d D hk0 hk hπ
    (smoothHorizontalIntegralInput d (successiveHorizontalEquationMap d hπ t')) = _
  rw [successiveHorizontalEquationMap_t, smoothHorizontalIntegralInput_apply,
    smoothHorizontalIntegralFirstResidue_base, smoothHorizontalFirstResidue_scale]

/-- The transported first slope retains the original branch value. -/
theorem smoothSuccessiveFirstResidueInput_v :
    smoothSuccessiveFirstResidueInput d hπ D hk0 hk v = 0 := by
  change smoothSuccessiveFirstIntegralResidue d hπ D hk0 hk
    (smoothSuccessiveIntegralInput d hπ v) = _
  rw [← modificationMap_v W (π ^ k) π d.b3 d.b4 d.b6,
    smoothSuccessiveIntegralInput_original, smoothSuccessiveFirstIntegralResidue_base]
  change smoothHorizontalIntegralFirstResidue d D hk0 hk hπ
    (smoothHorizontalIntegralInput d (successiveHorizontalEquationMap d hπ v')) = _
  rw [successiveHorizontalEquationMap_v, smoothHorizontalIntegralInput_apply,
    smoothHorizontalIntegralFirstResidue_base, smoothHorizontalFirstResidue_branch]

/-- The transported first input lies in the original incidence open. -/
theorem smoothSuccessiveFirstResidueInput_unit :
    IsUnit (smoothSuccessiveFirstResidueInput d hπ D hk0 hk t) := by
  rw [smoothSuccessiveFirstResidueInput_t]
  exact smoothHorizontalConic_incidence_unit D

/-- The retained horizontal coordinate vanishes on the transported first input. -/
theorem smoothSuccessiveFirstResidueInput_u :
    smoothSuccessiveFirstResidueInput d hπ D hk0 hk u = 0 :=
  horizontal_zero_of_incidence_unit W (π ^ k) π d.b3 d.b4 d.b6 _
    (smoothSuccessiveFirstResidueInput_unit d hπ D hk0 hk)
    (smoothHorizontalResidue_pi_zero D)

/-- The second input obtained by specializing the actual integral transport. -/
def smoothSuccessiveSecondResidueInput : A →ₐ[R] C :=
  (smoothSuccessiveSecondIntegralResidue d hπ D hk0 hk).comp
    (smoothSuccessiveIntegralInput d hπ)

/-- The transported second incidence retains its original signed conic coordinate. -/
theorem smoothSuccessiveSecondResidueInput_t :
    smoothSuccessiveSecondResidueInput d hπ D hk0 hk t =
      smoothHorizontalResidueConic D (-LaurentPolynomial.C a * LaurentPolynomial.T 1) := by
  change smoothSuccessiveSecondIntegralResidue d hπ D hk0 hk
    (smoothSuccessiveIntegralInput d hπ t) = _
  rw [← modificationMap_t W (π ^ k) π d.b3 d.b4 d.b6,
    smoothSuccessiveIntegralInput_original, smoothSuccessiveSecondIntegralResidue_base]
  change smoothHorizontalIntegralSecondResidue d D hk0 hk hπ
    (smoothHorizontalIntegralInput d (successiveHorizontalEquationMap d hπ t')) = _
  rw [successiveHorizontalEquationMap_t, smoothHorizontalIntegralInput_apply,
    smoothHorizontalIntegralSecondResidue_base, smoothHorizontalSecondResidue_scale]

/-- The transported second slope retains the original branch value. -/
theorem smoothSuccessiveSecondResidueInput_v :
    smoothSuccessiveSecondResidueInput d hπ D hk0 hk v = -algebraMap R C W.a₁ := by
  change smoothSuccessiveSecondIntegralResidue d hπ D hk0 hk
    (smoothSuccessiveIntegralInput d hπ v) = _
  rw [← modificationMap_v W (π ^ k) π d.b3 d.b4 d.b6,
    smoothSuccessiveIntegralInput_original, smoothSuccessiveSecondIntegralResidue_base]
  change smoothHorizontalIntegralSecondResidue d D hk0 hk hπ
    (smoothHorizontalIntegralInput d (successiveHorizontalEquationMap d hπ v')) = _
  rw [successiveHorizontalEquationMap_v, smoothHorizontalIntegralInput_apply,
    smoothHorizontalIntegralSecondResidue_base, smoothHorizontalSecondResidue_branch]
  rw [AlgHom.commutes]

/-- The transported second input lies in the original incidence open. -/
theorem smoothSuccessiveSecondResidueInput_unit :
    IsUnit (smoothSuccessiveSecondResidueInput d hπ D hk0 hk t) := by
  rw [smoothSuccessiveSecondResidueInput_t]
  exact smoothHorizontalConic_opposite_incidence_unit D

/-- The retained horizontal coordinate vanishes on the transported second input. -/
theorem smoothSuccessiveSecondResidueInput_u :
    smoothSuccessiveSecondResidueInput d hπ D hk0 hk u = 0 :=
  horizontal_zero_of_incidence_unit W (π ^ k) π d.b3 d.b4 d.b6 _
    (smoothSuccessiveSecondResidueInput_unit d hπ D hk0 hk)
    (smoothHorizontalResidue_pi_zero D)

end FLT.Mazur.WeierstrassIntegralChart
