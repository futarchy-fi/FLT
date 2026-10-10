/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXExtendedCastEvaluation
/-!
# The original constant-vanishing fiber cast

The identity comparison at equal constant coefficients preserves incidence and
slope. The original three-line residue equivalence factors through precisely
this cast of the full fiber, without changing its tensor source.
-/

@[expose] public noncomputable section

open IsLocalRing
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (a c c' : R) (hc : c = c')
/-- The identity comparison after transporting an equal constant coefficient. -/
def fiberConstantCast : FiberCoordinate a c ≃ₐ[R] FiberCoordinate a c' := by rw [hc]
/-- Constant transport preserves the incidence function. -/
theorem fiberConstantCast_t : fiberConstantCast a c c' hc (fiberT a c) = fiberT a c' := by
  subst c'
  rfl
/-- Constant transport preserves the slope function. -/
theorem fiberConstantCast_v : fiberConstantCast a c c' hc (fiberV a c) = fiberV a c' := by
  subst c'
  rfl

variable [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hstrict : 2 * k < n)
local notation "K" => ResidueField R

/-- The original three-line tensor comparison is the full comparison followed by this cast. -/
theorem residueLinesEquiv_eq_constantCast :
    residueLinesEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict =
    (residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).trans
      (fiberConstantCast (residue R W.a₁) (residue R b6) 0
        ((residue_eq_zero_iff _).mpr
          (WeierstrassDilatation.divided_constant_mem D k hstrict b6 h6))) := rfl
end FLT.Mazur.WeierstrassModificationX
