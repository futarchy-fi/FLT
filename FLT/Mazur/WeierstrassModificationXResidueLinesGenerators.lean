/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConstantCast
public import FLT.Mazur.WeierstrassModificationXResidueNamedGenerators
/-!
# Original three-line generators and contraction functions

The constant cast is sealed together with its proved equality. The resulting
formulas evaluate the original tensor comparison and its original chart map.
In particular x and y are computed from the original equation, not postulated
as functions on a replacement normal form.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
section
variable {R : Type*} [CommRing R] (a c c' : R) (hc : c = c')
/-- Seal the constructed constant cast with its equality proof. -/
opaque fiberConstantSeal :
    {e : FiberCoordinate a c ≃ₐ[R] FiberCoordinate a c' // e = fiberConstantCast a c c' hc} :=
  ⟨fiberConstantCast a c c' hc, rfl⟩
/-- The sealed identity comparison at equal constant coefficients. -/
def fiberConstantSealedEquiv : FiberCoordinate a c ≃ₐ[R] FiberCoordinate a c' :=
  (fiberConstantSeal a c c' hc).val
/-- The sealed constant comparison equals the constructed cast. -/
theorem fiberConstantSealedEquiv_def :
    fiberConstantSealedEquiv a c c' hc = fiberConstantCast a c c' hc :=
  (fiberConstantSeal a c c' hc).property
/-- The sealed constant comparison retains incidence. -/
theorem fiberConstantSealedEquiv_t :
    fiberConstantSealedEquiv a c c' hc (fiberT a c) = fiberT a c' := by
  rw [fiberConstantSealedEquiv_def, fiberConstantCast_t]
/-- The sealed constant comparison retains slope. -/
theorem fiberConstantSealedEquiv_v :
    fiberConstantSealedEquiv a c c' hc (fiberV a c) = fiberV a c' := by
  rw [fiberConstantSealedEquiv_def, fiberConstantCast_v]
end
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hstrict : 2 * k < n)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "F" => FiberCoordinate a 0

/-- The original three-line tensor equivalence retains incidence. -/
theorem residueLinesEquiv_t :
    residueLinesEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
      ((1 : K) ⊗ₜ[R] t W (π ^ k) b3 b4 b6) = fiberT a 0 := by
  rw [residueLinesEquiv_eq_constantCast, ← fiberConstantSealedEquiv_def,
    AlgEquiv.trans_apply, residueFiberEquiv_t, fiberConstantSealedEquiv_t]

/-- The original three-line tensor equivalence retains slope. -/
theorem residueLinesEquiv_v :
    residueLinesEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict
      ((1 : K) ⊗ₜ[R] v W (π ^ k) b3 b4 b6) = fiberV a 0 := by
  rw [residueLinesEquiv_eq_constantCast, ← fiberConstantSealedEquiv_def,
    AlgEquiv.trans_apply, residueFiberEquiv_v, fiberConstantSealedEquiv_v]

/-- The original chart map into the actual three-line tensor fiber. -/
def residueLinesMap : Coordinate W (π ^ k) b3 b4 b6 →ₐ[R] F :=
  ((residueLinesEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- The chart map is the original equivalence applied to the pure tensor. -/
theorem residueLinesMap_apply (z : Coordinate W (π ^ k) b3 b4 b6) :
    residueLinesMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict z =
    residueLinesEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict ((1 : K) ⊗ₜ[R] z) := rfl

/-- The original incidence becomes the named three-line incidence. -/
theorem residueLinesMap_t :
    residueLinesMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict (t W (π ^ k) b3 b4 b6) =
    fiberT a 0 := by rw [residueLinesMap_apply, residueLinesEquiv_t]

/-- The original slope becomes the named three-line slope. -/
theorem residueLinesMap_v :
    residueLinesMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict (v W (π ^ k) b3 b4 b6) =
    fiberV a 0 := by rw [residueLinesMap_apply, residueLinesEquiv_v]

omit [IsDomain R] in
/-- Maximal-ideal coefficients vanish in the three-line fiber. -/
theorem residueLines_coefficient_zero (r : R) (hr : r ∈ maximalIdeal R) :
    algebraMap R F r = 0 := by
  rw [IsScalarTower.algebraMap_apply R K F, ResidueField.algebraMap_eq,
    (residue_eq_zero_iff r).mpr hr, map_zero]

/-- The original horizontal coordinate becomes v*(v+a) before middle depth. -/
theorem residueLinesMap_x :
    residueLinesMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict (x W (π ^ k) b3 b4 b6) =
    fiberV a 0 * (fiberV a 0 + algebraMap R F W.a₁) := by
  obtain ⟨hb3, hb4⟩ := WeierstrassDilatation.divided_linear_mem D k hk b3 b4 h3 h4
  rw [map_x_of_linear_zero W _ _ _ _ _
    (residueLines_coefficient_zero W.a₂ D.a₂_mem)
    (residueLines_coefficient_zero b3 hb3) (residueLines_coefficient_zero b4 hb4),
    residueLinesMap_v, residueLines_coefficient_zero b6
      (WeierstrassDilatation.divided_constant_mem D k hstrict b6 h6), zero_mul, sub_zero]

/-- The original vertical coordinate becomes v²*(v+a) before middle depth. -/
theorem residueLinesMap_y :
    residueLinesMap D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict (y W (π ^ k) b3 b4 b6) =
    fiberV a 0 ^ 2 * (fiberV a 0 + algebraMap R F W.a₁) := by
  rw [y, map_mul, residueLinesMap_x, residueLinesMap_v]
  ring
end FLT.Mazur.WeierstrassModificationX
