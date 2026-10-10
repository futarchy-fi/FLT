/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleComponents
public import FLT.Mazur.WeierstrassSuccessiveXTensorContraction

/-!
# Retained contraction on the actual middle residue components

The actual preceding divided chart contracts the conic to its origin.
On the line of slope r its original coordinates restrict to (u,r*u).
These formulas concern the original contraction inside the tensor fiber.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "f" => tensorPreviousMap W (π ^ k) π b3 b4 b6 K
local notation "x₀" => WeierstrassDilatation.x W (π ^ k) (π * b3) (π * b4) (π ^ 2 * b6)
local notation "y₀" => WeierstrassDilatation.y W (π ^ k) (π * b3) (π * b4) (π ^ 2 * b6)

/-- The original preceding horizontal function vanishes on the entire retained conic. -/
theorem residueSuccessiveConic_previous_x :
    residueSuccessiveConicMap D k hk0 hk b3 b4 b6 h3 h4 (f x₀) = 0 := by
  rw [tensorPreviousMap_x, residueSuccessiveConicMap_coord]
  rfl

/-- The original preceding vertical function also vanishes on that same full conic. -/
theorem residueSuccessiveConic_previous_y :
    residueSuccessiveConicMap D k hk0 hk b3 b4 b6 h3 h4 (f y₀) = 0 := by
  rw [tensorPreviousMap_y, map_mul, residueSuccessiveConicMap_coord]
  exact zero_mul _

/-- Restrict actual tensor functions to the line with the specified original tangent slope. -/
def residueSuccessiveLineMap (r : K) (hr : r * (r + residue R W.a₁) = 0) : T →ₐ[K] K[X] :=
  (middleLineMap (W.map (residue R)) (residue R b6)
    ((residue_eq_zero_iff _).mpr D.a₂_mem) r hr).comp
      (residueRetainedFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).toAlgHom

/-- Tensor restriction keeps the original free horizontal coordinate and its slope. -/
@[simp] theorem residueSuccessiveLineMap_coord
    (r : K) (hr : r * (r + residue R W.a₁) = 0) (i : Fin 3) :
    residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4 r hr
      (tensorCoord W (π ^ k) π b3 b4 b6 K i) = ![0, C r, X] i := by
  simp only [residueSuccessiveLineMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    residueRetainedFiberEquiv_coord, middleLineMap_coord]

/-- The original preceding horizontal function stays the actual line parameter. -/
theorem residueSuccessiveLine_previous_x
    (r : K) (hr : r * (r + residue R W.a₁) = 0) :
    residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4 r hr (f x₀) = X := by
  rw [tensorPreviousMap_x, residueSuccessiveLineMap_coord]
  rfl

/-- The original preceding vertical function retains the specified tangent slope. -/
theorem residueSuccessiveLine_previous_y
    (r : K) (hr : r * (r + residue R W.a₁) = 0) :
    residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4 r hr (f y₀) = X * C r := by
  rw [tensorPreviousMap_y, map_mul, residueSuccessiveLineMap_coord,
    residueSuccessiveLineMap_coord]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
