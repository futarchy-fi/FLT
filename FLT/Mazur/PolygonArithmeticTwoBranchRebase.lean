/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticTwoBranchFirstIdentification
public import FLT.Mazur.PolygonSmoothingParameterEquiv

/-!
# Rebasing a terminal correction before taking its geometric inverse

The product of the two scalar drift units determines the required target
smoothing. Dividing by this unit makes the correction start at the original
node, so its inverse on spectra has the direction needed for residual removal.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)

/-- The exact product of both scalar drift units, in composition order. -/
def twoBranchCorrectionDriftUnit (m : ℕ) (q : Bool → R[T;T⁻¹]) : (Quotient R π m)ˣ :=
  nilpotentMultiplier (parameter R π m) ⟨m + 1, parameter_pow R π m⟩
      (algebraMap R _ ((q true).coeff 1)) *
    nilpotentMultiplier (parameter R π m) ⟨m + 1, parameter_pow R π m⟩
      (algebraMap R _ ((q false).coeff 1))

/-- The two successive smoothing changes equal multiplication by this one unit. -/
theorem twoBranchCorrectionSmoothing_eq_drift (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) :
    twoBranchCorrectionSmoothing R π m t q = ↑(twoBranchCorrectionDriftUnit R π m q) * t := by
  simp only [twoBranchCorrectionSmoothing, correctionSmoothing,
    twoBranchCorrectionDriftUnit, Units.val_mul, nilpotentMultiplier_val, mul_assoc]

/-- The target smoothing needed to make the algebra correction start at the original node. -/
def twoBranchCorrectionRebasedSmoothing (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) : Quotient R π m :=
  ↑(twoBranchCorrectionDriftUnit R π m q)⁻¹ * t

/-- Both corrections on the rebased target have precisely the original source smoothing. -/
theorem twoBranchCorrectionRebasedSmoothing_source (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) :
    twoBranchCorrectionSmoothing R π m (twoBranchCorrectionRebasedSmoothing R π m t q) q = t := by
  rw [twoBranchCorrectionSmoothing_eq_drift, twoBranchCorrectionRebasedSmoothing,
    ← mul_assoc, Units.mul_inv, one_mul]

/-- The rebased smoothing recovers the original smoothing on the first layer. -/
theorem twoBranchCorrectionRebasedSmoothing_first (t : Quotient R π 1)
    (ht : parameter R π 1 * t = 0) (q : Bool → R[T;T⁻¹]) :
    twoBranchCorrectionRebasedSmoothing R π 1 t q = t := by
  have hv : ↑(twoBranchCorrectionDriftUnit R π 1 q) * t = t := by
    rw [← twoBranchCorrectionSmoothing_eq_drift, twoBranchCorrectionSmoothing_first R π t ht]
  unfold twoBranchCorrectionRebasedSmoothing
  calc
    _ = ↑(twoBranchCorrectionDriftUnit R π 1 q)⁻¹ *
        (↑(twoBranchCorrectionDriftUnit R π 1 q) * t) := by rw [hv]
    _ = t := by rw [← mul_assoc, Units.inv_mul, one_mul]

/-- The entire correction now starts at the original node, with its full constructed inverse. -/
irreducible_def twoBranchCorrectionRebasedFactor (m : ℕ) (t : Quotient R π m)
    (q : Bool → R[T;T⁻¹]) :
    ChartRing t ≃ₐ[Quotient R π m]
      ChartRing (twoBranchCorrectionRebasedSmoothing R π m t q) :=
  (nodeParameterEquiv t _ (twoBranchCorrectionRebasedSmoothing_source R π m t q).symm).trans
    (twoBranchCorrectionNodeFactor R π m (twoBranchCorrectionRebasedSmoothing R π m t q) q)

end FLT.Mazur.PolygonArithmeticStages
