/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCoefficients
public import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# A plane presentation of the actual divided chart

Identify the existing monic coordinate algebra with the quotient of the
polynomial plane by its single actual equation. This makes both partial
derivatives available for smooth neighborhoods, even at nonunit scale.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The actual divided equation on the polynomial plane. -/
def planeEquation : MvPolynomial (Fin 2) R :=
  X 1 ^ 2 + (C W.a₁ * X 0 + C b3) * X 1 -
    (C s * X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C b4 * X 0 + C b6)

/-- The one-relation plane quotient of the divided equation. -/
abbrev PlaneCoordinate := MvPolynomial (Fin 2) R ⧸
  Ideal.span (Set.range (fun _ : Unit => planeEquation W s b3 b4 b6))

local notation "A" => Coordinate W s b3 b4 b6
local notation "P" => PlaneCoordinate W s b3 b4 b6
local notation "q" => Ideal.Quotient.mkₐ R
  (Ideal.span (Set.range (fun _ : Unit => planeEquation W s b3 b4 b6)))

/-- The two generators of the plane quotient satisfy the divided equation. -/
theorem planeCoordinate_equation :
    q (X 1) ^ 2 + (algebraMap R P W.a₁ * q (X 0) + algebraMap R P b3) * q (X 1) =
      algebraMap R P s * q (X 0) ^ 3 + algebraMap R P W.a₂ * q (X 0) ^ 2 +
        algebraMap R P b4 * q (X 0) + algebraMap R P b6 := by
  have h : q (planeEquation W s b3 b4 b6) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(), rfl⟩)
  have hc (z : R) : q (C z) = algebraMap R P z := rfl
  change q (X 1 ^ 2 + (C W.a₁ * X 0 + C b3) * X 1 -
    (C s * X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C b4 * X 0 + C b6)) = 0 at h
  simpa only [map_sub, map_add, map_mul, map_pow, hc, sub_eq_zero] using h

/-- Evaluate the existing coordinate algebra in its plane quotient. -/
def toPlaneCoordinate : A →ₐ[R] P :=
  evaluation W s b3 b4 b6 (q (X 0)) (q (X 1)) (planeCoordinate_equation W s b3 b4 b6)

/-- Evaluate the polynomial plane back in the existing coordinate algebra. -/
def fromPlaneCoordinate : P →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (aeval ![x W s b3 b4 b6, y W s b3 b4 b6]) (by
    change Ideal.span _ ≤ RingHom.ker (aeval ![x W s b3 b4 b6, y W s b3 b4 b6])
    apply Ideal.span_le.mpr
    rintro _ ⟨u, rfl⟩
    change aeval _ (planeEquation W s b3 b4 b6) = 0
    simpa only [planeEquation, map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_eq_zero] using
      equation W s b3 b4 b6)

/-- The quotient comparison sends each plane generator to the corresponding actual coordinate. -/
theorem fromPlaneCoordinate_mk (i : Fin 2) :
    fromPlaneCoordinate W s b3 b4 b6 (q (X i)) =
      ![x W s b3 b4 b6, y W s b3 b4 b6] i := by
  simp [fromPlaneCoordinate]

/-- The plane comparison fixes both generators of the existing algebra. -/
theorem fromPlaneCoordinate_comp :
    (fromPlaneCoordinate W s b3 b4 b6).comp (toPlaneCoordinate W s b3 b4 b6) =
      AlgHom.id R A := by
  apply hom_ext <;>
    simp [toPlaneCoordinate, fromPlaneCoordinate]

/-- The reverse comparison fixes all functions on the polynomial plane quotient. -/
theorem toPlaneCoordinate_comp :
    (toPlaneCoordinate W s b3 b4 b6).comp (fromPlaneCoordinate W s b3 b4 b6) =
      AlgHom.id R P := by
  apply Ideal.Quotient.algHom_ext
  ext i
  fin_cases i <;>
    simp [fromPlaneCoordinate, toPlaneCoordinate]

/-- The actual divided algebra and its one-relation plane presentation agree. -/
def planeCoordinateEquiv : A ≃ₐ[R] P :=
  AlgEquiv.ofAlgHom (toPlaneCoordinate W s b3 b4 b6) (fromPlaneCoordinate W s b3 b4 b6)
    (toPlaneCoordinate_comp W s b3 b4 b6) (fromPlaneCoordinate_comp W s b3 b4 b6)

end FLT.Mazur.WeierstrassDilatation
