/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffinePointCoordinates

/-!
# The regular Vélu morphism agrees with the original point map off the kernel

The actual scheme morphism specializes to the target chart point given by
the original xMap and yMap sums, retaining the original source evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  {x y : K} (hP : E.toAffine.Nonsingular x y) (hPG : Affine.Point.some x y hP ∉ G)

/-- The actual target chart point defined by the original Vélu coordinate sums. -/
def veluTargetPointChart : Coordinate (curve E G) 2 →ₐ[K] K :=
  evaluation (curve E G) 2 ![xMap E G (.some x y hP), yMap E G (.some x y hP), 1]
    ((Projective.equation_some _ _).mpr
      (by simpa using equation_xMap_yMap E G hodd hP hPG)) rfl

/-- Evaluating the regular chart map gives exactly the original target point. -/
theorem veluAffineRegularChart_point :
    (veluAffinePointLift E G hP hPG).comp (veluAffineRegularChart E G hodd) =
      veluTargetPointChart E G hodd hP hPG := by
  apply hom_ext
  intro i
  fin_cases i
  · change veluAffinePointLift E G hP hPG
      (veluAffineRegularChart E G hodd (coord (curve E G) 2 0)) =
        veluTargetPointChart E G hodd hP hPG (coord (curve E G) 2 0)
    rw [veluAffineRegularChart, veluTargetPointChart, evaluation_coord, evaluation_coord]
    exact veluAffinePointLift_x E G hP hPG hodd
  · change veluAffinePointLift E G hP hPG
      (veluAffineRegularChart E G hodd (coord (curve E G) 2 1)) =
        veluTargetPointChart E G hodd hP hPG (coord (curve E G) 2 1)
    rw [veluAffineRegularChart, veluTargetPointChart, evaluation_coord, evaluation_coord]
    exact veluAffinePointLift_y E G hP hPG hodd
  · change ((veluAffinePointLift E G hP hPG).comp (veluAffineRegularChart E G hodd))
      (coord (curve E G) 2 2) = veluTargetPointChart E G hodd hP hPG (coord (curve E G) 2 2)
    rw [coord_self, map_one, map_one]

/-- The actual regular scheme morphism specializes to the original Vélu target point. -/
@[reassoc] theorem veluAffineRegularMorphism_point :
    Spec.map (CommRingCat.ofHom (veluAffinePointLift E G hP hPG).toRingHom) ≫
        veluAffineRegularMorphism E G hodd =
      Spec.map (CommRingCat.ofHom (veluTargetPointChart E G hodd hP hPG).toRingHom) ≫
        integralCurveChart (curve E G) 2 := by
  rw [veluAffineRegularMorphism, ← Spec.map_comp_assoc]
  have h := congrArg AlgHom.toRingHom (veluAffineRegularChart_point E G hodd hP hPG)
  change Spec.map (CommRingCat.ofHom
    ((veluAffinePointLift E G hP hPG).comp (veluAffineRegularChart E G hodd)).toRingHom) ≫ _ = _
  rw [h]

end WeierstrassCurve.Velu
