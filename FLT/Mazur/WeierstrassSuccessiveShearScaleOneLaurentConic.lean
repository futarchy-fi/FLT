/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearTerminalZeroConicCoordinates
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentConic
public import FLT.Mazur.LaurentUnitPoints
public import FLT.Mazur.WeierstrassDilatationShearLaurentNormalForm
public import FLT.Mazur.WeierstrassModificationXConicBoundaryParameters

/-!
# The actual scale-one terminal Laurent boundary

The entire terminal equation restricts along the actual integral transition.
Its Laurent coordinate is the original conic slope divided by incidence;
the two ordered parameter formulas retain the nonzero divided constant.
-/

@[expose] public noncomputable section
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (π : R)
  (k : ℕ) (b3 b4 b6 : R) (S : Type u) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S (π ^ k) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S b6
local notation "C₀" => ConicCoordinate (U).a₁ c
local notation "B" => MiddleConicOpen U c
local notation "T₀" => ScalarExtension W (π ^ k) π b3 b4 b6 S
local notation "D" => S ⊗[R] WeierstrassDilatation.Coordinate W (π ^ (k + 1)) b3 b4 b6
local notation "x" => WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6
local notation "y" => WeierstrassDilatation.y W (π ^ (k + 1)) b3 b4 b6
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
variable (hc : IsUnit (algebraMap R S b6))
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (k + 1)) = 0 from by
  rw [pow_succ, map_mul, hp, mul_zero]
local notation "E" => tensorShearTerminalLaurentEquiv W π k b3 b4 b6 S r hp h3 h4 hr hc a ha
local notation "φ" => tensorShearScaleOneTerminalConicMap W π k b3 b4 b6 S r hs hp h3 h4 hr
local notation "v" => conicBoundaryUnit U c
local notation "tx" => (1 : S) ⊗ₜ[R] x
local notation "ty" => (1 : S) ⊗ₜ[R] y

/-- The full terminal Laurent algebra restricts along the actual integral conic transition. -/
def tensorShearScaleOneTerminalLaurentConicMap : S[T;T⁻¹] →ₐ[S] B :=
  (φ).comp (E).symm.toAlgHom

local notation "ψ" => tensorShearScaleOneTerminalLaurentConicMap W π k b3 b4 b6 S r
  hs hp h3 h4 hr hc a ha

/-- The first ordered tangent factor restricts to the unshifted slope divided by incidence. -/
theorem tensorShearScaleOneTerminalLaurentConicMap_parameter : ψ (LaurentPolynomial.T 1) =
    (↑v⁻¹ : B) * algebraMap C₀ B (conicV (U).a₁ c) := by
  have H : E (ty - algebraMap S D r * tx) = LaurentPolynomial.T 1 := by
    rw [map_sub, map_mul, AlgEquiv.commutes,
      tensorShearTerminalLaurent_y, tensorShearTerminalLaurent_x]
    change _ + LaurentPolynomial.C r * _ - LaurentPolynomial.C r * _ = _
    ring
  rw [← H]
  change φ ((E).symm ((E) (ty - algebraMap S D r * tx))) = _
  rw [AlgEquiv.symm_apply_apply, map_sub, map_mul, AlgHom.commutes,
    tensorShearScaleOneTerminalConicMap_x W π k b3 b4 b6 S r hs hp h3 h4 hr,
    tensorShearScaleOneTerminalConicMap_y W π k b3 b4 b6 S r hs hp h3 h4 hr]
  ring

/-- The complete Laurent coordinate is exactly the original incidence slope. -/
theorem tensorShearScaleOneTerminalLaurentConicMap_slope :
    ψ (LaurentPolynomial.T 1) = conicIncidenceSlope (U).a₁ c := by
  rw [tensorShearScaleOneTerminalLaurentConicMap_parameter,
    tensorShearTerminalLaurent_incidenceInverse]
  rfl

/-- The full first ordered parameter retains its actual divided-constant scale. -/
theorem tensorShearScaleOneTerminalLaurentConicMap_firstParameter :
    ψ (LaurentPolynomial.T 1) =
      algebraMap S B c * conicIncidenceFirstParameter (U).a₁ c hc := by
  rw [tensorShearScaleOneTerminalLaurentConicMap_slope, conicIncidenceSlope_first]

/-- The inverse Laurent coordinate is the complete second ordered parameter. -/
theorem tensorShearScaleOneTerminalLaurentConicMap_inverseParameter :
    ψ (LaurentPolynomial.T (-1)) = conicIncidenceSecondParameter (U).a₁ c hc := by
  have hu : IsUnit (ψ (LaurentPolynomial.T 1)) :=
    (LaurentPolynomial.isUnit_T 1).map ψ
  apply hu.mul_left_cancel
  rw [← map_mul, ← LaurentPolynomial.T_add, show (1 : ℤ) + -1 = 0 from rfl,
    LaurentPolynomial.T_zero, map_one, tensorShearScaleOneTerminalLaurentConicMap_slope,
    conicIncidenceSlope_second]

/-- The whole boundary map agrees with the positive-scale presentation, at every function.
The auxiliary depth is used only to present the same conic/Laurent gluing. -/
theorem tensorShearScaleOneTerminalLaurentConicMap_eq :
    ψ = tensorShearTerminalLaurentConicMap W π (k + 1) b3 b4 b6 S r
      hsNext hp h3 h4 hr hc a ha := by
  apply LaurentUnitPoints.hom_ext
  · rw [tensorShearScaleOneTerminalLaurentConicMap_slope,
      tensorShearTerminalLaurentConicMap_slope]
  · rw [tensorShearScaleOneTerminalLaurentConicMap_inverseParameter,
      tensorShearTerminalLaurentConicMap_inverseParameter]

end FLT.Mazur.WeierstrassSuccessiveX
