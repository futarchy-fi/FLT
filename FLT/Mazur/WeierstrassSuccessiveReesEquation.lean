/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXReesChart
public import FLT.Mazur.BlowupReesGeneratorCover

/-!
# The homogeneous equation of the successive Rees center

The degree-one vertical generator satisfies a quadratic in the ideal of
the scale and horizontal generators. Thus the vertical chart contributes
no points outside their union, including on the exceptional fiber.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BY" => WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6

/-- The homogeneous generator π*T of the actual preceding center. -/
def scaleGenerator : reesAlgebra I :=
  BlowupRees.generator I (algebraMap R B π) (Ideal.subset_span (by simp))

/-- The homogeneous generator x*T of the actual preceding center. -/
def horizontalGenerator : reesAlgebra I :=
  BlowupRees.generator I BX (Ideal.subset_span (by simp))

/-- The homogeneous generator y*T of the actual preceding center. -/
def verticalGenerator : reesAlgebra I :=
  BlowupRees.generator I BY (Ideal.subset_span (by simp))

local notation "P" => scaleGenerator W s π b3 b4 b6
local notation "X" => horizontalGenerator W s π b3 b4 b6
local notation "Y" => verticalGenerator W s π b3 b4 b6
local notation "c" => RingHom.comp (algebraMap B (reesAlgebra I)) (algebraMap R B)

/-- The divided cubic gives an exact quadratic relation among the three Rees generators. -/
theorem generator_equation :
    Y ^ 2 = X * ((c s * algebraMap B (reesAlgebra I) BX + c W.a₂) * X +
      c b4 * P - c W.a₁ * Y) + P * (c b6 * P - c b3 * Y) := by
  apply Subtype.ext
  change Polynomial.monomial 1 BY ^ 2 =
    Polynomial.monomial 1 BX *
      ((Polynomial.C (algebraMap R B s) * Polynomial.C BX +
        Polynomial.C (algebraMap R B W.a₂)) * Polynomial.monomial 1 BX +
        Polynomial.C (algebraMap R B b4) * Polynomial.monomial 1 (algebraMap R B π) -
        Polynomial.C (algebraMap R B W.a₁) * Polynomial.monomial 1 BY) +
      Polynomial.monomial 1 (algebraMap R B π) *
        (Polynomial.C (algebraMap R B b6) * Polynomial.monomial 1 (algebraMap R B π) -
          Polynomial.C (algebraMap R B b3) * Polynomial.monomial 1 BY)
  have he := congrArg (Polynomial.C : B →+* Polynomial B)
    (WeierstrassDilatation.equation W s (π * b3) (π * b4) (π ^ 2 * b6))
  simp only [map_add, map_mul, map_pow] at he
  simp only [← Polynomial.C_mul_X_eq_monomial]
  linear_combination Polynomial.X ^ 2 * he

/-- Every prime containing π*T and x*T also contains y*T. -/
theorem verticalGenerator_mem_of_scale_horizontal (J : Ideal (reesAlgebra I)) [J.IsPrime]
    (hP : P ∈ J) (hX : X ∈ J) : Y ∈ J := by
  apply (Ideal.IsPrime.pow_mem_iff_mem (inferInstance : J.IsPrime) 2 (by decide)).mp
  rw [generator_equation]
  exact J.add_mem (J.mul_mem_right _ hX) (J.mul_mem_right _ hP)

end FLT.Mazur.WeierstrassSuccessiveRees
