/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueGeometry
public import FLT.Mazur.WeierstrassDilatationExtendedTangent
public import FLT.Mazur.WeierstrassDilatationResidueRetained

/-!
# Explicit tangent coordinates of the original divided residue fiber

The existing tensor comparison sends the horizontal coordinate to the
scaled difference of tangent factors, and the vertical coordinate to the first factor.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
local notation "K" => ResidueField R
local notation "a" => residueTangentUnit D
local notation "c" => residue R b6

/-- The original comparison factors through the generic coefficient transport. -/
theorem residueCoordinateEquiv_eq_extendedTangent :
    residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4 =
      extendedTangentEquiv W (π ^ k) b3 b4 b6 a
        (show algebraMap R K (π ^ k) = 0 from residue_scale_eq_zero D k hk0)
        (show algebraMap R K b3 = 0 from (residue_eq_zero_iff _).mpr
          (divided_linear_mem D k hk b3 b4 h3 h4).1)
        (show algebraMap R K b4 = 0 from (residue_eq_zero_iff _).mpr
          (divided_linear_mem D k hk b3 b4 h3 h4).2)
        (residueTangentUnit_val D).symm ((residue_eq_zero_iff _).mpr D.a₂_mem) := rfl

/-- The coefficient comparison preserves the actual horizontal coordinate formula. -/
theorem residueCoordinateEquiv_x :
    residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4
      (x (W.map (residue R)) (residue R (π ^ k)) (residue R b3)
        (residue R b4) c) =
      algebraMap K _ (↑(a)⁻¹ : K) * (NodalFiber.q c - NodalFiber.p c) := by
  rw [residueCoordinateEquiv_eq_extendedTangent]
  erw [← extendedTangentSealedEquiv_def]
  exact extendedTangentSealedEquiv_x W (π ^ k) b3 b4 b6 a _ _ _ _ _

/-- The coefficient comparison preserves the actual vertical coordinate formula. -/
theorem residueCoordinateEquiv_y :
    residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4
      (y (W.map (residue R)) (residue R (π ^ k)) (residue R b3)
        (residue R b4) c) = NodalFiber.p c := by
  rw [residueCoordinateEquiv_eq_extendedTangent]
  erw [← extendedTangentSealedEquiv_def]
  exact extendedTangentSealedEquiv_y W (π ^ k) b3 b4 b6 a _ _ _ _ _

/-- Retain the original coefficient comparison and its proved equality behind a seal. -/
opaque residueCoordinateBoundedSeal :
    {e : ExtendedCoordinate W (π ^ k) b3 b4 b6 K ≃ₐ[K] NodalFiber.Coordinate c //
      e = residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4} :=
  ⟨residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4, rfl⟩

/-- Seal the coefficient comparison before evaluating the tensor composition. -/
def residueCoordinateBoundedEquiv :
    ExtendedCoordinate W (π ^ k) b3 b4 b6 K ≃ₐ[K] NodalFiber.Coordinate c :=
  (residueCoordinateBoundedSeal D k hk0 hk b3 b4 b6 h3 h4).val

/-- The sealed comparison equals the original coefficient map. -/
theorem residueCoordinateBoundedEquiv_def :
    residueCoordinateBoundedEquiv D k hk0 hk b3 b4 b6 h3 h4 =
      residueCoordinateEquiv D k hk0 hk b3 b4 b6 h3 h4 :=
  (residueCoordinateBoundedSeal D k hk0 hk b3 b4 b6 h3 h4).property

/-- The tensor comparison factors through the same sealed coefficient map. -/
theorem residueFiberEquiv_eq_bounded :
    residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4 =
      (baseChangeEquiv W (π ^ k) b3 b4 b6 K).trans
        (residueCoordinateBoundedEquiv D k hk0 hk b3 b4 b6 h3 h4) := by
  rw [residueCoordinateBoundedEquiv_def]
  rfl

/-- The sealed coefficient map retains the original x formula. -/
theorem residueCoordinateBoundedEquiv_x :
    residueCoordinateBoundedEquiv D k hk0 hk b3 b4 b6 h3 h4
      (x (W.map (residue R)) (residue R (π ^ k)) (residue R b3)
        (residue R b4) c) = algebraMap K _ (↑(a)⁻¹ : K) * (NodalFiber.q c - NodalFiber.p c) := by
  exact (congrArg (fun e => e
    (x (W.map (residue R)) (residue R (π ^ k)) (residue R b3) (residue R b4) c))
      (residueCoordinateBoundedEquiv_def D k hk0 hk b3 b4 b6 h3 h4)).trans
        (residueCoordinateEquiv_x D k hk0 hk b3 b4 b6 h3 h4)

/-- The sealed coefficient map retains the original y formula. -/
theorem residueCoordinateBoundedEquiv_y :
    residueCoordinateBoundedEquiv D k hk0 hk b3 b4 b6 h3 h4
      (y (W.map (residue R)) (residue R (π ^ k)) (residue R b3)
        (residue R b4) c) = NodalFiber.p c := by
  exact (congrArg (fun e => e
    (y (W.map (residue R)) (residue R (π ^ k)) (residue R b3) (residue R b4) c))
      (residueCoordinateBoundedEquiv_def D k hk0 hk b3 b4 b6 h3 h4)).trans
        (residueCoordinateEquiv_y D k hk0 hk b3 b4 b6 h3 h4)

/-- The full tensor horizontal coordinate is the tangent difference divided by a₁. -/
@[simp] theorem residueFiberEquiv_x :
    residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4 (tensorX W (π ^ k) b3 b4 b6 K) =
      algebraMap K _ (↑(a)⁻¹ : K) * (NodalFiber.q c - NodalFiber.p c) := by
  rw [residueFiberEquiv_eq_bounded, AlgEquiv.trans_apply, baseChangeEquiv_tensorX]
  exact residueCoordinateBoundedEquiv_x D k hk0 hk b3 b4 b6 h3 h4

/-- The full tensor vertical coordinate is the first tangent factor. -/
@[simp] theorem residueFiberEquiv_y :
    residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4 (tensorY W (π ^ k) b3 b4 b6 K) =
      NodalFiber.p c := by
  rw [residueFiberEquiv_eq_bounded, AlgEquiv.trans_apply, baseChangeEquiv_tensorY]
  exact residueCoordinateBoundedEquiv_y D k hk0 hk b3 b4 b6 h3 h4

end FLT.Mazur.WeierstrassDilatation
