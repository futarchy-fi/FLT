/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleConic

/-!
# The whole successive middle fiber as an extension of the actual conic

Adjoining the original horizontal coordinate u to the conic imposes exactly
t*u = 0. Explicit inverse maps identify the entire three-coordinate fiber,
including its scheme structure, with this conic polynomial quotient.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (c : R) (h2 : W.a₂ = 0)
local notation "A" => Coordinate W 0 0 0 0 c
local notation "C₀" => ConicCoordinate W.a₁ c

/-- Adjoin the retained horizontal variable to the conic with precisely the incidence relation. -/
abbrev MiddleExtension := AdjoinRoot (C (conicT W.a₁ c) * X)

/-- The retained horizontal variable in the conic extension. -/
def middleExtensionU : MiddleExtension W c := AdjoinRoot.root _

/-- The conic extension retains the original t*u = 0 equation. -/
theorem middleExtension_incidence :
    algebraMap C₀ (MiddleExtension W c) (conicT W.a₁ c) * middleExtensionU W c = 0 := by
  have h := AdjoinRoot.eval₂_root (C (conicT W.a₁ c) * X)
  simpa only [eval₂_mul, eval₂_C, eval₂_X, AdjoinRoot.algebraMap_eq,
    middleExtensionU] using h

/-- The conic extension maps to the actual middle fiber by the original generators. -/
def middleExtensionToCoordinate : MiddleExtension W c →ₐ[R] A :=
  AdjoinRoot.liftAlgHom (C (conicT W.a₁ c) * X) (middleConicSection W c h2)
    (coord W 0 0 0 0 c 2) (by
      simpa only [eval₂_mul, eval₂_C, eval₂_X, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, middleConicSection_t, map_zero] using incidence W 0 0 0 0 c)

/-- The extension map agrees with the original conic section on all conic functions. -/
theorem middleExtensionToCoordinate_base (z : C₀) :
    middleExtensionToCoordinate W c h2 (algebraMap C₀ (MiddleExtension W c) z) =
      middleConicSection W c h2 z := by
  simp only [middleExtensionToCoordinate, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.liftAlgHom_of]

/-- The new horizontal generator remains exactly the original u. -/
@[simp] theorem middleExtensionToCoordinate_u :
    middleExtensionToCoordinate W c h2 (middleExtensionU W c) = coord W 0 0 0 0 c 2 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The actual middle fiber evaluates in the full conic extension. -/
def coordinateToMiddleExtension : A →ₐ[R] MiddleExtension W c :=
  evaluation W 0 0 0 0 c
    ![algebraMap C₀ (MiddleExtension W c) (conicT W.a₁ c),
      algebraMap C₀ (MiddleExtension W c) (conicV W.a₁ c), middleExtensionU W c]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h2, map_zero,
        zero_mul, zero_add, add_zero]
      have h := congrArg (algebraMap C₀ (MiddleExtension W c)) (conic_relation W.a₁ c)
      simp only [map_sub, map_mul, map_add, map_pow, map_zero,
        ← IsScalarTower.algebraMap_apply R C₀] at h
      linear_combination h)
    (by
      change algebraMap C₀ (MiddleExtension W c) (conicT W.a₁ c) *
        middleExtensionU W c = algebraMap R (MiddleExtension W c) 0
      rw [map_zero]
      exact middleExtension_incidence W c)

/-- All three original generators are retained in the conic extension. -/
@[simp] theorem coordinateToMiddleExtension_coord (i : Fin 3) :
    coordinateToMiddleExtension W c h2 (coord W 0 0 0 0 c i) =
      ![algebraMap C₀ (MiddleExtension W c) (conicT W.a₁ c),
        algebraMap C₀ (MiddleExtension W c) (conicV W.a₁ c),
        middleExtensionU W c] i := evaluation_coord _ _ _ _ _ _ _ _ _ i

/-- The entire middle fiber, without reduction, is the conic extension with t*u = 0. -/
def middleExtensionEquiv : A ≃ₐ[R] MiddleExtension W c := by
  apply AlgEquiv.ofAlgHom (coordinateToMiddleExtension W c h2)
    (middleExtensionToCoordinate W c h2)
  · apply AdjoinRoot.algHom_ext'
    · apply conic_hom_ext
      · change coordinateToMiddleExtension W c h2
          (middleExtensionToCoordinate W c h2
          (algebraMap C₀ (MiddleExtension W c) (conicT W.a₁ c))) = _
        rw [middleExtensionToCoordinate_base, middleConicSection_t,
          coordinateToMiddleExtension_coord]
        rfl
      · change coordinateToMiddleExtension W c h2
          (middleExtensionToCoordinate W c h2
          (algebraMap C₀ (MiddleExtension W c) (conicV W.a₁ c))) = _
        rw [middleExtensionToCoordinate_base, middleConicSection_v,
          coordinateToMiddleExtension_coord]
        rfl
    · change coordinateToMiddleExtension W c h2
        (middleExtensionToCoordinate W c h2 (middleExtensionU W c)) = _
      rw [middleExtensionToCoordinate_u, coordinateToMiddleExtension_coord]
      rfl
  · apply hom_ext
    intro i
    change middleExtensionToCoordinate W c h2
      (coordinateToMiddleExtension W c h2 (coord W 0 0 0 0 c i)) = _
    rw [coordinateToMiddleExtension_coord]
    fin_cases i
    · exact (middleExtensionToCoordinate_base W c h2 _).trans (middleConicSection_t W c h2)
    · exact (middleExtensionToCoordinate_base W c h2 _).trans (middleConicSection_v W c h2)
    · exact middleExtensionToCoordinate_u W c h2

end FLT.Mazur.WeierstrassSuccessiveX
