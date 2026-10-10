/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleConic
public import FLT.Mazur.WeierstrassSuccessiveXLocalization

/-!
# The actual middle overlap lies entirely on the retained conic

Inverting t forces u = 0. The full overlap algebra is therefore the conic
localized at its original incidence coordinate. The existing transition to
the next divided chart is retained by composition of actual algebra maps.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "O" => XOpen W 0 0 0 0 c
local notation "C₀" => ConicCoordinate W.a₁ c

/-- The actual incidence principal open of the retained middle conic. -/
abbrev MiddleConicOpen := Localization.Away (conicT W.a₁ c)

/-- The retained horizontal coordinate vanishes on the entire incidence overlap. -/
theorem middle_overlap_u : algebraMap A O (coord W 0 0 0 0 c 2) = 0 := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := O) (coord W 0 0 0 0 c 0)).mul_left_cancel
  rw [mul_zero, ← map_mul, incidence, map_zero, map_zero]

/-- Restrict the actual successive overlap to the original conic overlap. -/
def middleOverlapToConic : O →ₐ[R] MiddleConicOpen W c :=
  IsLocalization.Away.liftAlgHom (coord W 0 0 0 0 c 0)
    (f := (IsScalarTower.toAlgHom R C₀ (MiddleConicOpen W c)).comp (middleConicMap W c h2))
    (by
      change IsUnit (algebraMap C₀ (MiddleConicOpen W c)
        (middleConicMap W c h2 (coord W 0 0 0 0 c 0)))
      rw [middleConicMap_coord]
      exact IsLocalization.Away.algebraMap_isUnit
        (S := MiddleConicOpen W c) (conicT W.a₁ c))

/-- The actual conic section gives the reverse map on the incidence overlap. -/
def middleConicToOverlap : MiddleConicOpen W c →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (conicT W.a₁ c)
    (f := (IsScalarTower.toAlgHom R A O).comp (middleConicSection W c h2)) (by
      change IsUnit (algebraMap A O (middleConicSection W c h2 (conicT W.a₁ c)))
      rw [middleConicSection_t]
      exact IsLocalization.Away.algebraMap_isUnit (S := O) _)

/-- Forward restriction agrees with the original conic map on every fiber function. -/
@[simp] theorem middleOverlapToConic_base (z : A) :
    middleOverlapToConic W c h2 (algebraMap A O z) =
      algebraMap C₀ (MiddleConicOpen W c) (middleConicMap W c h2 z) := by
  rw [middleOverlapToConic, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The reverse map is the original conic section on every conic function. -/
@[simp] theorem middleConicToOverlap_base (z : C₀) :
    middleConicToOverlap W c h2 (algebraMap C₀ (MiddleConicOpen W c) z) =
      algebraMap A O (middleConicSection W c h2 z) := by
  rw [middleConicToOverlap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The whole successive overlap is precisely the incidence-open part of the actual conic. -/
def middleOverlapConicEquiv : O ≃ₐ[R] MiddleConicOpen W c := by
  apply AlgEquiv.ofAlgHom (middleOverlapToConic W c h2) (middleConicToOverlap W c h2)
  · apply IsLocalization.algHom_ext (Submonoid.powers (conicT W.a₁ c))
    apply conic_hom_ext
    · change middleOverlapToConic W c h2
        (middleConicToOverlap W c h2 (algebraMap C₀ _ (conicT W.a₁ c))) = _
      rw [middleConicToOverlap_base, middleConicSection_t,
        middleOverlapToConic_base, middleConicMap_coord]
      rfl
    · change middleOverlapToConic W c h2
        (middleConicToOverlap W c h2 (algebraMap C₀ _ (conicV W.a₁ c))) = _
      rw [middleConicToOverlap_base, middleConicSection_v,
        middleOverlapToConic_base, middleConicMap_coord]
      rfl
  · apply IsLocalization.algHom_ext (Submonoid.powers (coord W 0 0 0 0 c 0))
    refine hom_ext W 0 0 0 0 c (S := O) _ _ ?_
    intro i
    change middleConicToOverlap W c h2
      (middleOverlapToConic W c h2 (algebraMap A O (coord W 0 0 0 0 c i))) = _
    rw [middleOverlapToConic_base, middleConicToOverlap_base, middleConicMap_coord]
    fin_cases i
    · change algebraMap A O (middleConicSection W c h2 (conicT W.a₁ c)) =
        algebraMap A O (coord W 0 0 0 0 c 0)
      rw [middleConicSection_t]
    · change algebraMap A O (middleConicSection W c h2 (conicV W.a₁ c)) =
        algebraMap A O (coord W 0 0 0 0 c 1)
      rw [middleConicSection_v]
    · change algebraMap A O (middleConicSection W c h2 0) =
        algebraMap A O (coord W 0 0 0 0 c 2)
      rw [map_zero, map_zero, middle_overlap_u]

/-- The existing next divided-chart overlap is the same original conic incidence open. -/
def middleDividedConicOverlap : DividedOpen W 0 0 0 0 c ≃ₐ[R] MiddleConicOpen W c :=
  (overlapEquiv W 0 0 0 0 c).trans (middleOverlapConicEquiv W c h2)

end FLT.Mazur.WeierstrassSuccessiveX
