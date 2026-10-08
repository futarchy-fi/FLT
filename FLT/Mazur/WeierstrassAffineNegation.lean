/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicPolarization
public import FLT.Mazur.WeierstrassIntegralChart

/-!
# Negation on the integral affine chart

The projective involution [X:Y:Z] ↦ [X:-Y-a₁X-a₃Z:Z] preserves the cubic
and the affine normalization. It defines an actual involutive algebra map,
without a discriminant assumption or division by two.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Homogeneous negation of the universal point on any chart. -/
def chartNegationCoordinates (j : Fin 3) : Fin 3 → Coordinate W j :=
  ![coord W j 0, (W.map (algebraMap R _)).toProjective.negY (coord W j), coord W j 2]

/-- Negation coordinates satisfy the homogeneous cubic over the original chart ring. -/
theorem chartNegationCoordinates_equation (j : Fin 3) :
    (W.map (algebraMap R (Coordinate W j))).toProjective.Equation
      (chartNegationCoordinates W j) :=
  projective_equation_negate _ (coord_equation W j)

/-- The normalized affine negation morphism, contravariantly on coordinate rings. -/
def affineNegation : Coordinate W 2 →ₐ[R] Coordinate W 2 :=
  evaluation W 2 (chartNegationCoordinates W 2) (chartNegationCoordinates_equation W 2)
    (coord_self W 2)

/-- Every coordinate of affine negation is its original homogeneous formula. -/
@[simp] theorem affineNegation_coord (i : Fin 3) :
    affineNegation W (coord W 2 i) = chartNegationCoordinates W 2 i :=
  evaluation_coord W 2 _ _ _ i

/-- Negation leaves the affine X coordinate unchanged. -/
theorem affineNegation_x : affineNegation W (coord W 2 0) = coord W 2 0 :=
  affineNegation_coord W 0

/-- The affine Y coordinate changes by the usual integral Weierstrass formula. -/
theorem affineNegation_y :
    affineNegation W (coord W 2 1) = -coord W 2 1 -
      algebraMap R _ W.a₁ * coord W 2 0 - algebraMap R _ W.a₃ := by
  simp [chartNegationCoordinates, Projective.negY]

/-- Applying the actual affine algebra map twice gives the identity. -/
theorem affineNegation_comp :
    (affineNegation W).comp (affineNegation W) = AlgHom.id R (Coordinate W 2) := by
  apply hom_ext
  intro i
  fin_cases i
  · change affineNegation W (affineNegation W (coord W 2 0)) = coord W 2 0
    rw [affineNegation_x, affineNegation_x]
  · change affineNegation W (affineNegation W (coord W 2 1)) = coord W 2 1
    simp only [affineNegation_y, map_sub, map_neg, map_mul,
      AlgHom.commutes, affineNegation_x]
    ring
  · change affineNegation W (affineNegation W (coord W 2 2)) = coord W 2 2
    simp only [coord_self, map_one]

/-- Affine negation is an algebra automorphism over the coefficient ring. -/
def affineNegationEquiv : Coordinate W 2 ≃ₐ[R] Coordinate W 2 :=
  AlgEquiv.ofAlgHom (affineNegation W) (affineNegation W)
    (affineNegation_comp W) (affineNegation_comp W)

/-- The coordinate formulas commute with every coefficient-preserving specialization. -/
theorem chartNegationCoordinates_map (j : Fin 3) (f : Coordinate W j →ₐ[R] S) :
    f ∘ chartNegationCoordinates W j =
      ![f (coord W j 0), (W.map (algebraMap R S)).toProjective.negY (f ∘ coord W j),
        f (coord W j 2)] := by
  ext i
  fin_cases i <;>
    simp [chartNegationCoordinates, Projective.negY, AlgHom.commutes]

end FLT.Mazur.WeierstrassIntegralChart
