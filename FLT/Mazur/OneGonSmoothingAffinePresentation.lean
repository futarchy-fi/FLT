/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingEquation
public import FLT.Mazur.OneGonQuotient
public import FLT.Mazur.WeierstrassIntegralChart

/-!
# The zero-parameter affine chart is the original plane cubic

The two explicit quotient maps preserve x and y. Composing this comparison
with the original pinching presentation will identify the actual node chart.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open MvPolynomial WeierstrassCurve WeierstrassIntegralChart PolygonNodePresentation
variable {R : Type*} [CommRing R]

/-- The original two-variable plane quotient. -/
abbrev Plane := MvPolynomial (Fin 2) R ⧸ bRelation

/-- The retained plane coordinates. -/
def planeCoord (i : Fin 2) : Plane (R := R) := Ideal.Quotient.mk _ (X i)

/-- The original relation holds in the two-variable quotient. -/
theorem planeCoord_relation :
    planeCoord (R := R) 1 ^ 2 - planeCoord 0 * planeCoord 1 - planeCoord 0 ^ 3 = 0 := by
  change Ideal.Quotient.mk (bRelation (R := R)) (bEquation (R := R)) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- The plane coordinates give the normalized zero-parameter projective solution. -/
theorem planeCoord_equation :
    ((equation (0 : R)).map (algebraMap R (Plane (R := R)))).toProjective.Equation
      ![planeCoord 0, planeCoord 1, 1] := by
  rw [Projective.equation_iff]
  simp only [Projective.fin3_def_ext, equation, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, map_neg, map_one, map_zero]
  linear_combination planeCoord_relation (R := R)

/-- Evaluate the normalized three-coordinate quotient in the original plane quotient. -/
def zeroAffineToPlane : Coordinate (equation (0 : R)) 2 →ₐ[R] Plane (R := R) :=
  evaluation _ 2 ![planeCoord 0, planeCoord 1, 1] planeCoord_equation rfl

/-- The zero-parameter affine coordinates obey the original pinching equation. -/
theorem zeroAffine_relation :
    coord (equation (0 : R)) 2 1 ^ 2 -
      coord (equation (0 : R)) 2 0 * coord (equation (0 : R)) 2 1 -
      coord (equation (0 : R)) 2 0 ^ 3 = 0 := by
  have h := coord_equation (equation (0 : R)) 2
  rw [Projective.equation_iff] at h
  simp only [coord_self] at h
  dsimp only [WeierstrassCurve.toProjective, WeierstrassCurve.map, equation] at h
  simp only [map_neg, map_one, map_zero] at h
  dsimp only [equation]
  linear_combination h

/-- Evaluate the original plane quotient in the normalized affine chart. -/
def planeToZeroAffine : Plane (R := R) →ₐ[R] Coordinate (equation (0 : R)) 2 :=
  Ideal.Quotient.liftₐ _
    (aeval ![coord (equation (0 : R)) 2 0, coord (equation (0 : R)) 2 1]) (by
      change bRelation ≤ RingHom.ker (aeval
        ![coord (equation (0 : R)) 2 0, coord (equation (0 : R)) 2 1]).toRingHom
      rw [bRelation, Ideal.span_le, Set.singleton_subset_iff]
      change aeval _ bEquation = 0
      simpa [bEquation] using zeroAffine_relation (R := R))

/-- The reverse map preserves the two actual coordinate generators. -/
@[simp] theorem planeToZeroAffine_coord (i : Fin 2) :
    planeToZeroAffine (planeCoord (R := R) i) = coord (equation (0 : R)) 2 i.castSucc := by
  fin_cases i <;> simp [planeCoord, planeToZeroAffine]

/-- Removing the normalized third coordinate gives an explicit algebra equivalence. -/
def zeroAffinePlaneEquiv : Coordinate (equation (0 : R)) 2 ≃ₐ[R] Plane (R := R) :=
  AlgEquiv.ofAlgHom zeroAffineToPlane planeToZeroAffine (by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change zeroAffineToPlane (planeToZeroAffine (planeCoord i)) = planeCoord i
    fin_cases i <;> simp [zeroAffineToPlane]) (by
    apply hom_ext
    intro i
    fin_cases i <;> simp [zeroAffineToPlane, coord_self])

/-- The forward equivalence retains the first coordinate. -/
@[simp] theorem zeroAffinePlaneEquiv_x :
    zeroAffinePlaneEquiv (coord (equation (0 : R)) 2 0) = planeCoord 0 := by
  simp [zeroAffinePlaneEquiv, zeroAffineToPlane]

/-- The forward equivalence retains the second coordinate. -/
@[simp] theorem zeroAffinePlaneEquiv_y :
    zeroAffinePlaneEquiv (coord (equation (0 : R)) 2 1) = planeCoord 1 := by
  simp [zeroAffinePlaneEquiv, zeroAffineToPlane]

end FLT.Mazur.OneGonSmoothing
