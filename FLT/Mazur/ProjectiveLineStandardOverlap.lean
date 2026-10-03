/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineStandardCharts
public import FLT.Mazur.BinaryOpenDescent
/-!
# Laurent overlap of the standard projective line

The intersection of the two homogeneous charts is their localization at the
coordinate ratio. Polynomial chart coordinates identify it with the Laurent
ring, and the second coordinate becomes its inverse. The resulting cartesian
open cover is also a pushout.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial LaurentPolynomial
universe u
namespace FLT.Mazur.ProjectiveLineStandardOverlap
open ProjectiveSpace ProjectiveLineStandardCharts
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous overlap is the Laurent polynomial ring. -/
def overlapRingEquiv : overlapRing K (Fin 2) 0 1 ≃+* K[T;T⁻¹] :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (coordinate K (Fin 2) 0 1))
    (T := Submonoid.powers (Polynomial.X : K[X])) _ _ (leftRingEquiv K).toRingEquiv (by
    rw [Submonoid.map_powers]
    congr 1
    exact leftRingEquiv_coordinate K)

@[simp] theorem overlapRingEquiv_left (p : chartRing K (Fin 2) 0) :
    overlapRingEquiv K (chartOverlapLeft K (Fin 2) 0 1 p) =
      Polynomial.toLaurent (leftRingEquiv K p) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ p

@[simp] theorem overlapRingEquiv_scalar (r : K) :
    overlapRingEquiv K (algebraMap K (overlapRing K (Fin 2) 0 1) r) =
      LaurentPolynomial.C r := by
  rw [← (chartOverlapLeft K (Fin 2) 0 1).commutes r]
  rw [overlapRingEquiv_left]
  change Polynomial.toLaurent (leftRingEquiv K (chartScalars K (Fin 2) 0 r)) = _
  simp

/-- The coordinate of the second chart is the inverse Laurent coordinate. -/
theorem overlapRingEquiv_inverseCoordinate :
    overlapRingEquiv K (chartOverlapRight K (Fin 2) 0 1 (coordinate K (Fin 2) 1 0)) =
      LaurentPolynomial.T (-1) := by
  have h := congrArg (overlapRingEquiv K) (chartOverlap_coordinate K (Fin 2) 0 1 0)
  simp only [coordinate_self, map_one, map_mul, overlapRingEquiv_left,
    leftRingEquiv_coordinate, Polynomial.toLaurent_X] at h
  let z := overlapRingEquiv K
    (chartOverlapRight K (Fin 2) 0 1 (coordinate K (Fin 2) 1 0))
  change z = LaurentPolynomial.T (-1)
  change 1 = z * LaurentPolynomial.T 1 at h
  calc
    z = z * (LaurentPolynomial.T 1 * LaurentPolynomial.T (-1)) := by
      rw [← LaurentPolynomial.T_add]
      simp only [show (1 : ℤ) + -1 = 0 from rfl, LaurentPolynomial.T_zero, mul_one]
    _ = (z * LaurentPolynomial.T 1) * LaurentPolynomial.T (-1) := (mul_assoc _ _ _).symm
    _ = LaurentPolynomial.T (-1) := by rw [← h, one_mul]

/-- Restriction to the second chart uses reciprocal coordinates. -/
theorem overlapRingEquiv_right :
    (overlapRingEquiv K).toRingHom.comp (chartOverlapRight K (Fin 2) 0 1).toRingHom =
      LaurentPolynomial.invert.toRingHom.comp
        (Polynomial.toLaurent.comp (rightRingEquiv K).toRingHom) := by
  apply chartRing_hom_ext
  · intro r
    change overlapRingEquiv K (chartOverlapRight K (Fin 2) 0 1
      (algebraMap K _ r)) = LaurentPolynomial.invert (Polynomial.toLaurent
        (rightRingEquiv K (chartScalars K (Fin 2) 1 r)))
    rw [AlgHom.commutes, overlapRingEquiv_scalar, rightRingEquiv_scalar]
    simp
  · intro i
    fin_cases i
    · change overlapRingEquiv K (chartOverlapRight K (Fin 2) 0 1
        (coordinate K (Fin 2) 1 0)) = LaurentPolynomial.invert
          (Polynomial.toLaurent (rightRingEquiv K (coordinate K (Fin 2) 1 0)))
      rw [overlapRingEquiv_inverseCoordinate, rightRingEquiv_coordinate]
      simp
    · simp

/-- Identify the existing Laurent spectrum with the homogeneous overlap. -/
def overlapSpecIso : ProjectiveLine.overlap K ≅ Spec (.of (overlapRing K (Fin 2) 0 1)) :=
  Scheme.Spec.mapIso (overlapRingEquiv K).toCommRingCatIso.op

@[reassoc] theorem overlapSpecIso_left :
    (overlapSpecIso K).hom ≫
      Spec.map (CommRingCat.ofHom (chartOverlapLeft K (Fin 2) 0 1).toRingHom) =
      ProjectiveLine.overlapLeft K ≫ (leftSpecIso K).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (overlapRingEquiv_left K)

@[reassoc] theorem overlapSpecIso_right :
    (overlapSpecIso K).hom ≫
      Spec.map (CommRingCat.ofHom (chartOverlapRight K (Fin 2) 0 1).toRingHom) =
      ProjectiveLine.overlapRight K ≫ (rightSpecIso K).hom := by
  rw [ProjectiveLine.overlapRight, ProjectiveLine.inversion_hom, Category.assoc]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact overlapRingEquiv_right K

/-- The specified reciprocal Laurent transition agrees inside Proj. -/
theorem condition :
    ProjectiveLine.overlapLeft K ≫ left K = ProjectiveLine.overlapRight K ≫ right K := by
  rw [left, right, ← Category.assoc, ← Category.assoc,
    ← overlapSpecIso_left, ← overlapSpecIso_right, Category.assoc, Category.assoc,
    chartOverlapLeft_chartMap, chartOverlapRight_chartMap]

/-- The Laurent chart is the actual intersection of the two polynomial charts. -/
theorem isPullback : IsPullback (ProjectiveLine.overlapLeft K)
    (ProjectiveLine.overlapRight K) (left K) (right K) := by
  apply (chartOverlapIsPullback K (Fin 2) 0 1).of_iso (overlapSpecIso K).symm
    (leftSpecIso K).symm (rightSpecIso K).symm (Iso.refl _)
  · rw [← cancel_epi (overlapSpecIso K).hom]
    rw [← Category.assoc, overlapSpecIso_left]
    simp
  · rw [← cancel_epi (overlapSpecIso K).hom]
    rw [← Category.assoc, overlapSpecIso_right]
    simp
  · simp [left]
  · simp [right]

/-- The standard projective line is the specified two-chart gluing. -/
theorem isPushout : IsPushout (ProjectiveLine.overlapLeft K)
    (ProjectiveLine.overlapRight K) (left K) (right K) :=
  BinaryOpenDescent.isPushout _ _ _ _ (isPullback K) (covers K)
end FLT.Mazur.ProjectiveLineStandardOverlap
