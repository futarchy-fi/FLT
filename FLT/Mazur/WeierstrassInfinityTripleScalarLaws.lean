/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleScalarMaps
public import FLT.Mazur.WeierstrassInfinitySpecializedFactorization

/-!
# Actual scalar equations on the all-infinity member

All four line equations, divided cubics and unit normalizers are derived from
the genuine maps and expressed in the seven actual point coordinates.
These statements impose no extra open condition on the full-cover member.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- Scalar form of each genuine left-input compatibility. -/
theorem infinityTripleScalarLaw_left_coord (j : Fin 4) (i : Fin 3) :
    infinityTripleScalarLaw W hΔ j (infinityInputLeft W (coord W 1 i)) =
      infinityTripleScalarPoint W hΔ (infinityTripleLeftIndex j) (coord W 1 i) :=
  DFunLike.congr_fun (infinityTripleScalarLaw_left W hΔ j) _

/-- Scalar form of each genuine right-input compatibility. -/
theorem infinityTripleScalarLaw_right_coord (j : Fin 4) (i : Fin 3) :
    infinityTripleScalarLaw W hΔ j (infinityInputRight W (coord W 1 i)) =
      infinityTripleScalarPoint W hΔ (infinityTripleRightIndex j) (coord W 1 i) :=
  DFunLike.congr_fun (infinityTripleScalarLaw_right W hΔ j) _

/-- Scalar form of each genuine output identification. -/
theorem infinityTripleScalarLaw_output_coord (j : Fin 4) (i : Fin 3) :
    infinityTripleScalarLaw W hΔ j (infinityAdditionChart W (coord W 1 i)) =
      infinityTripleScalarPoint W hΔ (infinityTripleOutputIndex j) (coord W 1 i) :=
  DFunLike.congr_fun (infinityTripleScalarLaw_output W hΔ j) _

/-- The actual four slopes satisfy their line equations in one common section ring. -/
theorem infinityTripleScalar_line (j : Fin 4) :
    infinityTripleScalarSlope W hΔ j *
        (infinityTripleScalarX W hΔ (infinityTripleRightIndex j) -
          infinityTripleScalarX W hΔ (infinityTripleLeftIndex j)) =
      infinityTripleScalarZ W hΔ (infinityTripleRightIndex j) -
        infinityTripleScalarZ W hΔ (infinityTripleLeftIndex j) := by
  simpa only [infinityTripleScalarX, infinityTripleScalarZ, infinityTripleScalarSlope,
    infinityTripleScalarLaw_left_coord, infinityTripleScalarLaw_right_coord] using
    infinitySpecialization_line W (infinityTripleScalarLaw W hΔ j)

/-- The divided cubic equation retains tangent information for all four laws. -/
theorem infinityTripleScalar_cubic (j : Fin 4) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    let a := infinityTripleLeftIndex j
    let b := infinityTripleRightIndex j
    infinityTripleScalarSlope W hΔ j * infinitySlopeDenominator V (x b) (z a) (z b) =
      infinitySlopeNumerator V (x a) (x b) (z a) := by
  simpa only [infinityTripleScalarX, infinityTripleScalarZ, infinityTripleScalarSlope,
    infinityTripleScalarLaw_left_coord, infinityTripleScalarLaw_right_coord] using
    infinitySpecialization_cubic W (infinityTripleScalarLaw W hΔ j)

/-- All four chosen slope denominators are units on the actual intersection. -/
theorem infinityTripleScalar_den_unit (j : Fin 4) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let x := infinityTripleScalarX W hΔ
    let z := infinityTripleScalarZ W hΔ
    IsUnit (infinitySlopeDenominator V (x (infinityTripleRightIndex j))
      (z (infinityTripleLeftIndex j)) (z (infinityTripleRightIndex j))) := by
  simpa only [infinityTripleScalarX, infinityTripleScalarZ,
    infinityTripleScalarLaw_left_coord, infinityTripleScalarLaw_right_coord] using
    infinitySpecialization_den_unit W (infinityTripleScalarLaw W hΔ j)

/-- The four actual output normalizers remain units in the common section ring. -/
theorem infinityTripleScalar_scale_unit (j : Fin 4) :
    IsUnit (infinityTripleScalarScale W hΔ j) :=
  (infinityOutputY_isUnit W).map (infinityTripleScalarLaw W hΔ j)

/-- Clearing the actual output unit recovers the homogeneous formula. -/
theorem infinityTripleScalar_coord_mul (j : Fin 4) (i : Fin 3) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    infinityTripleScalarPoint W hΔ (infinityTripleOutputIndex j) (coord W 1 i) *
        infinityTripleScalarScale W hΔ j =
      infinityAdditionXYZ V (infinityTripleScalarX W hΔ (infinityTripleLeftIndex j))
        (infinityTripleScalarX W hΔ (infinityTripleRightIndex j))
        (infinityTripleScalarZ W hΔ (infinityTripleLeftIndex j))
        (infinityTripleScalarSlope W hΔ j) i := by
  have h := infinitySpecialization_coord_mul W (infinityTripleScalarLaw W hΔ j) i
  rw [← infinitySpecialization_homogeneous W (infinityTripleScalarLaw W hΔ j) 1] at h
  simpa only [infinityTripleScalarX, infinityTripleScalarZ, infinityTripleScalarSlope,
    infinityTripleScalarScale, infinityTripleScalarLaw_left_coord,
    infinityTripleScalarLaw_right_coord, infinityTripleScalarLaw_output_coord] using h

/-- Each actual output's negated Y coordinate gives the leading coefficient after scaling. -/
theorem infinityTripleScalar_negY (j : Fin 4) :
    let V := W.map (algebraMap R Γ(InfinityTripleFull W hΔ, ⊤))
    let k := infinityTripleOutputIndex j
    (-1 - V.a₁ * infinityTripleScalarX W hΔ k - V.a₃ * infinityTripleScalarZ W hΔ k) *
        infinityTripleScalarScale W hΔ j =
      infinityLineLeading V (infinityTripleScalarSlope W hΔ j) := by
  simpa only [infinityTripleScalarX, infinityTripleScalarZ, infinityTripleScalarSlope,
    infinityTripleScalarScale, infinityTripleScalarLaw_output_coord] using
    infinitySpecialization_output_negY W (infinityTripleScalarLaw W hΔ j)

end FLT.Mazur.WeierstrassIntegralChart
