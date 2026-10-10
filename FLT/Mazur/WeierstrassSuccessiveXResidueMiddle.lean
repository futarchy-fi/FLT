/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXBaseChangeCoordinates
public import FLT.Mazur.WeierstrassSuccessiveXParameterEquiv
public import FLT.Mazur.WeierstrassDilatationResidueDepth

/-!
# Successive residue fibers with the middle coefficient retained

The tensor fiber keeps t*u = 0 and v²+a₁*v = b₆*t². The divided
constant is not discarded: at exact middle depth its residue is a unit.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6)
local notation "K" => ResidueField R

/-- Normalize the residue equation while retaining the actual divided constant. -/
def residueRetainedEquiv : ExtendedCoordinate W (π ^ k) π b3 b4 b6 K ≃ₐ[K]
    Coordinate (W.map (residue R)) 0 0 0 0 (residue R b6) := by
  obtain ⟨hb3, hb4⟩ := WeierstrassDilatation.divided_linear_mem D (k + 1)
    hk b3 b4 h3 h4
  apply parameterEquiv _ _ _ _ _ _ _ _ _ _ _
  · exact WeierstrassDilatation.residue_scale_eq_zero D k hk0
  · exact (residue_eq_zero_iff _).mpr
      (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  · exact (residue_eq_zero_iff _).mpr hb3
  · exact (residue_eq_zero_iff _).mpr hb4
  · rfl

/-- All three coordinates survive residue normalization at and before middle depth. -/
@[simp] theorem residueRetainedEquiv_coord (i : Fin 3) :
    residueRetainedEquiv D k hk0 hk b3 b4 b6 h3 h4
      (extendedCoord W (π ^ k) π b3 b4 b6 K i) =
        coord (W.map (residue R)) 0 0 0 0 (residue R b6) i :=
  parameterEquiv_coord _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl i

/-- The actual tensor residue fiber retains the middle-depth constant and incidence. -/
def residueRetainedFiberEquiv : ScalarExtension W (π ^ k) π b3 b4 b6 K ≃ₐ[K]
    Coordinate (W.map (residue R)) 0 0 0 0 (residue R b6) :=
  (baseChangeEquiv W (π ^ k) π b3 b4 b6 K).trans
    (residueRetainedEquiv D k hk0 hk b3 b4 b6 h3 h4)

/-- The full tensor comparison preserves each original generator. -/
@[simp] theorem residueRetainedFiberEquiv_coord (i : Fin 3) :
    residueRetainedFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
      (tensorCoord W (π ^ k) π b3 b4 b6 K i) =
        coord (W.map (residue R)) 0 0 0 0 (residue R b6) i := by
  simp only [residueRetainedFiberEquiv, AlgEquiv.trans_apply, baseChangeEquiv_coord,
    residueRetainedEquiv_coord]

omit [IsDomain R] in
include D h6 in
/-- At exact middle depth the retained constant is a unit in the residue field. -/
theorem residue_middle_constant_unit (hm : 2 * (k + 1) = n) : IsUnit (residue R b6) :=
  (WeierstrassDilatation.divided_constant_isUnit D (k + 1) hm b6 h6).map (residue R)

end FLT.Mazur.WeierstrassSuccessiveX
