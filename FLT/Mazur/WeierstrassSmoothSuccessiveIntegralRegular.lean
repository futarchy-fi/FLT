/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothSuccessiveIntegralTransport

/-!
# Regular coefficients on the common integral action refinement

Flatness of the original input and of the incidence localization transports
regular coefficients from the horizontal equation algebra. The incidence
relation then proves regularity of the actual original output x coordinate.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassModificationReesCoordinates WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} {k : ℕ}
  (d : WeierstrassDividedDepth.Data W π (k + 1)) (hπ : π ≠ 0)
local notation "H" => WeierstrassModificationX.horizontalReesChart W (π ^ (k + 1))
local notation "O" => SmoothHorizontalActionRing d
local notation "L" => SmoothSuccessiveActionOpen d hπ
local notation "B" => WeierstrassModificationX.Coordinate W (π ^ k * π) d.b3 d.b4 d.b6
local notation "A" => WeierstrassSuccessiveX.Coordinate W (π ^ k) π d.b3 d.b4 d.b6

include d hπ in
/-- Nonzero coefficients are regular in the original horizontal fraction chart. -/
theorem successiveHorizontal_base_regular {r : R} (hr : r ≠ 0) :
    IsRegular (algebraMap R H r) := by
  let E := WeierstrassModificationX.horizontalReesChartEquiv W (π ^ (k + 1))
    d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero _ hπ)
  have h := flatRingHom_isRegular E.toAlgHom.toRingHom
    (RingHom.Flat.of_bijective E.bijective)
    (WeierstrassModificationX.base_regular W (π ^ (k + 1)) d.b3 d.b4 d.b6
      (pow_ne_zero _ hπ) hr)
  change IsRegular (E (algebraMap R _ r)) at h
  rwa [E.commutes] at h

/-- The named common incidence refinement is flat over the original action source. -/
theorem smoothSuccessiveActionOpen_flat : RingHom.Flat (algebraMap O L) :=
  RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The common refinement still has a flat original horizontal input. -/
theorem smoothSuccessiveActionOpen_input_flat :
    RingHom.Flat ((algebraMap O L).comp (smoothHorizontalIntegralInput d).toRingHom) :=
  (smoothHorizontalIntegralInput_flat d).comp (smoothSuccessiveActionOpen_flat d hπ)

/-- No nonzero original coefficient acquires torsion on the common integral refinement. -/
theorem smoothSuccessiveActionOpen_base_regular {r : R} (hr : r ≠ 0) :
    IsRegular (algebraMap R L r) := by
  have hb : IsRegular (algebraMap R (HorizontalSourceRing W (π ^ (k + 1))) r) :=
    successiveHorizontal_base_regular d hπ hr
  have h := flatRingHom_isRegular _ (smoothSuccessiveActionOpen_input_flat d hπ) hb
  change IsRegular (algebraMap O L (smoothHorizontalIntegralInput d
    (algebraMap R (HorizontalSourceRing W (π ^ (k + 1))) r))) at h
  rwa [AlgHom.commutes, ← IsScalarTower.algebraMap_apply] at h

/-- The transported input retains a regular original horizontal coordinate. -/
theorem smoothSuccessiveIntegralInput_original_x_regular :
    IsRegular (smoothSuccessiveIntegralInput d hπ
      (modificationMap W (π ^ k) π d.b3 d.b4 d.b6
        (WeierstrassModificationX.x W (π ^ k * π) d.b3 d.b4 d.b6))) := by
  have h := congrArg (smoothSuccessiveIntegralInput d hπ)
    (congrArg (modificationMap W (π ^ k) π d.b3 d.b4 d.b6)
      (WeierstrassModificationX.incidence W (π ^ k * π) d.b3 d.b4 d.b6))
  simp only [map_mul, AlgHom.commutes] at h
  have hr := smoothSuccessiveActionOpen_base_regular d hπ
    (mul_ne_zero (pow_ne_zero k hπ) hπ)
  rw [map_mul, ← h] at hr
  exact hr.of_mul_right

/-- The genuine output retains a regular original x before either residue specialization. -/
theorem smoothSuccessiveIntegralOutput_original_x_regular :
    IsRegular (smoothSuccessiveIntegralOutput d hπ
      (modificationMap W (π ^ k) π d.b3 d.b4 d.b6
        (WeierstrassModificationX.x W (π ^ k * π) d.b3 d.b4 d.b6))) := by
  have h := congrArg (smoothSuccessiveIntegralOutput d hπ)
    (congrArg (modificationMap W (π ^ k) π d.b3 d.b4 d.b6)
      (WeierstrassModificationX.incidence W (π ^ k * π) d.b3 d.b4 d.b6))
  simp only [map_mul, AlgHom.commutes] at h
  have hr := smoothSuccessiveActionOpen_base_regular d hπ
    (mul_ne_zero (pow_ne_zero k hπ) hπ)
  rw [map_mul, ← h] at hr
  exact hr.of_mul_right

end FLT.Mazur.WeierstrassIntegralChart
