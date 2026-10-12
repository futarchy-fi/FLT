/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIncidenceShearNormalForm
public import FLT.Mazur.WeierstrassSuccessiveCoefficientShear
public import FLT.Mazur.WeierstrassSuccessiveXParameterEquiv
public import FLT.Mazur.WeierstrassSuccessiveXMiddleExtension
public import FLT.Mazur.WeierstrassSuccessiveXBaseChangeCoordinates

/-!
# Full retained equations after coefficient extension and tangent shear

The entire retained tensor equation becomes the original middle conic with
its horizontal variable and the relation t*u=0. No coordinate is inverted.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S] (r : S)
local notation "q" => algebraMap R S
local notation "U" => rootShearCurve (W.map q) r
local notation "c" => q b6
variable (hs : algebraMap R S s = 0) (hπ : algebraMap R S π = 0)
  (h3 : algebraMap R S b3 = 0) (h4 : algebraMap R S b4 = 0)

/-- The full sheared retained equation with its vanishing parameters normalized. -/
def coefficientShearMiddleEquiv :
    Coordinate U (q s) (q π) (q b3) (q b4 - r * q b3) c ≃ₐ[S]
      Coordinate U 0 0 0 0 c :=
  parameterEquiv U (q s) (q π) (q b3) (q b4 - r * q b3) c 0 0 0 0 c
    hs hπ h3 (by rw [h3, h4, mul_zero, sub_zero]) rfl

/-- All three sheared retained coordinates survive the parameter normalization. -/
theorem coefficientShearMiddleEquiv_coord (i : Fin 3) :
    coefficientShearMiddleEquiv W s π b3 b4 b6 S r hs hπ h3 h4
      (coord U (q s) (q π) (q b3) (q b4 - r * q b3) c i) = coord U 0 0 0 0 c i :=
  parameterEquiv_coord _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i

/-- The original tensor equation identifies the entire sheared middle equation. -/
def tensorShearMiddleEquiv : ScalarExtension W s π b3 b4 b6 S ≃ₐ[S]
    Coordinate U 0 0 0 0 c :=
  (successiveCoefficientShearEquiv W s π b3 b4 b6 S r).trans
    (coefficientShearMiddleEquiv W s π b3 b4 b6 S r hs hπ h3 h4)

/-- The actual original retained coordinates keep both incidence variables and the root shift. -/
theorem tensorShearMiddleEquiv_coord (i : Fin 3) :
    tensorShearMiddleEquiv W s π b3 b4 b6 S r hs hπ h3 h4
      (tensorCoord W s π b3 b4 b6 S i) =
        ![coord U 0 0 0 0 c 0, coord U 0 0 0 0 c 1 + algebraMap S _ r,
          coord U 0 0 0 0 c 2] i := by
  change coefficientShearMiddleEquiv W s π b3 b4 b6 S r hs hπ h3 h4
    (successiveCoefficientShearEquiv W s π b3 b4 b6 S r
      ((1 : S) ⊗ₜ[R] coord W s π b3 b4 b6 i)) = _
  rw [successiveCoefficientShearEquiv_tmul, one_smul, coefficientMap_coord, extendedCoord,
    shearForward_coord]
  fin_cases i <;> simp [coefficientShearMiddleEquiv_coord]

variable (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "h2" => WeierstrassModificationX.coefficientShear_a₂_zero W S r hr

/-- The complete original retained tensor algebra is the conic extension with t*u=0. -/
def tensorShearConicExtensionEquiv :
    ScalarExtension W s π b3 b4 b6 S ≃ₐ[S] MiddleExtension U c :=
  (tensorShearMiddleEquiv W s π b3 b4 b6 S r hs hπ h3 h4).trans
    (middleExtensionEquiv U c h2)

/-- The original horizontal function is the full retained variable, even at its zero locus. -/
theorem tensorShearConicExtensionEquiv_u :
    tensorShearConicExtensionEquiv W s π b3 b4 b6 S r hs hπ h3 h4 hr
      (tensorCoord W s π b3 b4 b6 S 2) = middleExtensionU U c := by
  change coordinateToMiddleExtension U c h2
    (tensorShearMiddleEquiv W s π b3 b4 b6 S r hs hπ h3 h4 _) = _
  rw [tensorShearMiddleEquiv_coord]
  exact coordinateToMiddleExtension_coord U c h2 2

end FLT.Mazur.WeierstrassSuccessiveX
