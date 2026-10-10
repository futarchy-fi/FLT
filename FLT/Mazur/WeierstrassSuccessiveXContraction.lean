/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXAlgebra
public import FLT.Mazur.WeierstrassDilatationRefinement

/-!
# Contraction of the successive x-direction chart

The new equation chart contracts to the preceding divided chart by (u,u*v).
Its incidence relation proves the preceding equation, including the original
cubic coefficient s. No cancellation or reducedness is needed for this map.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "T" => coord W s π b3 b4 b6 0
local notation "V" => coord W s π b3 b4 b6 1
local notation "U" => coord W s π b3 b4 b6 2

/-- The contracted coordinates solve the preceding divided equation. -/
theorem contraction_equation :
    (U * V) ^ 2 + (algebraMap R A W.a₁ * U + algebraMap R A (π * b3)) * (U * V) =
      algebraMap R A s * U ^ 3 + algebraMap R A W.a₂ * U ^ 2 +
        algebraMap R A (π * b4) * U + algebraMap R A (π ^ 2 * b6) := by
  simp only [map_mul, map_pow]
  rw [← incidence W s π b3 b4 b6]
  linear_combination U ^ 2 * equation W s π b3 b4 b6

/-- The coordinate map contracting one actual x-direction step. -/
def fromDivided :
    WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6) →ₐ[R] A :=
  WeierstrassDilatation.evaluation W s (π * b3) (π * b4) (π ^ 2 * b6)
    U (U * V) (contraction_equation W s π b3 b4 b6)

/-- The preceding horizontal coordinate is retained as the third generator. -/
@[simp] theorem fromDivided_x :
    fromDivided W s π b3 b4 b6
      (WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)) = U :=
  WeierstrassDilatation.evaluation_x _ _ _ _ _ _ _ _

/-- The preceding vertical coordinate is horizontal coordinate times slope. -/
@[simp] theorem fromDivided_y :
    fromDivided W s π b3 b4 b6
      (WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)) = U * V :=
  WeierstrassDilatation.evaluation_y _ _ _ _ _ _ _ _

open AlgebraicGeometry CategoryTheory

/-- The actual affine contraction onto the preceding divided chart. -/
def toDivided : Spec (.of A) ⟶
    Spec (.of (WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6))) :=
  Spec.map (CommRingCat.ofHom (fromDivided W s π b3 b4 b6).toRingHom)

/-- The successive x-direction chart retains the original projective cubic map. -/
def toCurve (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
    (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6)) :
    Spec (.of A) ⟶ WeierstrassIntegralChart.integralCurve W :=
  toDivided W s π b3 b4 b6 ≫
    WeierstrassDilatation.toCurve W s (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6

end FLT.Mazur.WeierstrassSuccessiveX
