/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingUnitBoundary
public import FLT.Mazur.NilpotentPolynomialEvaluation
public import FLT.Mazur.WeierstrassModificationXLaurentRoot

/-!
# Constructed slope roots on an entire retained arithmetic node

The divided coefficients live on the full node xy = π. Both the conic root
and the root including the original s*y term are constructed in its nilpotent
coefficient ideal, so no puncture or inverse coordinate is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
local notation "B" => ChartRing π
local notation "x" => leftCoordinate π
local notation "y" => rightCoordinate π
local notation "C" => algebraMap R B

/-- The linear coefficient on the whole retained node, using its actual divided coefficient. -/
def retainedSlopeLinear : B := C W.a₁ + C c3 * x

/-- The conic constant on the whole retained node, with the full quadratic correction. -/
def retainedConicConstant : B := C W.a₂ + C c4 * x + C c6 * x ^ 2

/-- The original slope equation retains the full smoothing term on the other branch. -/
def retainedSlopeConstant : B := retainedConicConstant W π c4 c6 + C s * y

variable (I : Ideal R) (hI : IsNilpotent I)
local notation "J" => I.map C

include hI in
/-- The original coefficient ideal remains nilpotent on the entire retained node. -/
theorem retainedArithmeticIdeal_nilpotent : IsNilpotent J :=
  NilpotentPolynomialInverse.mapIdeal_nilpotent I hI C

variable (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)

include hI ha h3 in
/-- The full retained linear coefficient is a unit before either branch is inverted. -/
theorem retainedSlopeLinear_unit : IsUnit (retainedSlopeLinear W π c3) := by
  have hn := NilpotentQuadraticRoot.element_nilpotent J
    (retainedArithmeticIdeal_nilpotent π I hI)
    ((J).mul_mem_right x (Ideal.mem_map_of_mem C h3))
  exact hn.isUnit_add_left_of_commute (ha.map C) (mul_comm _ _)

include h2 h4 h6 in
/-- Every term of the retained conic constant lies in the original coefficient ideal. -/
theorem retainedConicConstant_mem : retainedConicConstant W π c4 c6 ∈ J :=
  (J).add_mem ((J).add_mem (Ideal.mem_map_of_mem C h2)
    ((J).mul_mem_right x (Ideal.mem_map_of_mem C h4)))
    ((J).mul_mem_right (x ^ 2) (Ideal.mem_map_of_mem C h6))

include hs h2 h4 h6 in
/-- The full retained slope constant includes the original smoothing in the same ideal. -/
theorem retainedSlopeConstant_mem : retainedSlopeConstant W π s c4 c6 ∈ J :=
  (J).add_mem (retainedConicConstant_mem W π c4 c6 I h2 h4 h6)
    ((J).mul_mem_right y (Ideal.mem_map_of_mem C hs))

/-- The small conic root is constructed on the entire original retained node. -/
def retainedConicRoot : B :=
  NilpotentQuadraticRoot.root J (retainedArithmeticIdeal_nilpotent π I hI)
    (retainedSlopeLinear W π c3) (retainedConicConstant W π c4 c6)
    (retainedSlopeLinear_unit W π c3 I hI ha h3)
    (retainedConicConstant_mem W π c4 c6 I h2 h4 h6)

/-- The full small slope root is constructed before any original node coordinate is inverted. -/
def retainedSlopeRoot : B :=
  NilpotentQuadraticRoot.root J (retainedArithmeticIdeal_nilpotent π I hI)
    (retainedSlopeLinear W π c3) (retainedSlopeConstant W π s c4 c6)
    (retainedSlopeLinear_unit W π c3 I hI ha h3)
    (retainedSlopeConstant_mem W π s c4 c6 I hs h2 h4 h6)

/-- The constructed conic branch has its specified nilpotent reduction. -/
theorem retainedConicRoot_mem : retainedConicRoot W π c3 c4 c6 I hI ha h2 h3 h4 h6 ∈ J :=
  NilpotentQuadraticRoot.root_mem ..

/-- The constructed full slope branch has its specified nilpotent reduction. -/
theorem retainedSlopeRoot_mem : retainedSlopeRoot W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 ∈ J :=
  NilpotentQuadraticRoot.root_mem ..

/-- The entire retained conic equation holds on the constructed root. -/
theorem retainedConicRoot_equation :
    retainedConicRoot W π c3 c4 c6 I hI ha h2 h3 h4 h6 ^ 2 +
      retainedSlopeLinear W π c3 * retainedConicRoot W π c3 c4 c6 I hI ha h2 h3 h4 h6 =
        retainedConicConstant W π c4 c6 :=
  NilpotentQuadraticRoot.root_equation ..

/-- The full retained equation keeps the actual smoothing term on the other branch. -/
theorem retainedSlopeRoot_equation :
    retainedSlopeRoot W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 ^ 2 +
      retainedSlopeLinear W π c3 * retainedSlopeRoot W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 =
        retainedSlopeConstant W π s c4 c6 :=
  NilpotentQuadraticRoot.root_equation ..

end FLT.Mazur.WeierstrassModificationX
