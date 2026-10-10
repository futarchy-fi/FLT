/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueDividedOverlap
public import FLT.Mazur.WeierstrassSuccessiveXConicBoundaryCoordinates

/-!
# The exact divided tensor functions on the original conic boundary

The actual tensor transition preserves the reciprocal incidence and the
oriented slope ratio. These formulas concern original tensor functions,
not only their normalized special-fiber representatives.
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
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (k + 1)) b3 b4 b6 K
local notation "e₀" => WeierstrassDilatation.residueRetainedTensorEquiv
  b3 b4 b6 D (k + 1) (Nat.zero_lt_succ k) hk h3 h4
local notation "e" => AlgEquiv.trans e₀ (WeierstrassDilatation.parameterEquiv W₀
  0 (0 * 0) 0 0 c 0 0 c (Eq.symm (zero_mul 0)) rfl rfl rfl)

open WeierstrassModificationX
local notation "B" => MiddleConicOpen W₀ c
local notation "C₀" => ConicCoordinate (WeierstrassCurve.a₁ W₀) c
local notation "h2" => Iff.mpr (residue_eq_zero_iff _) D.a₂_mem
local notation "v" => conicBoundaryUnit W₀ c
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K
local notation "ty" => WeierstrassDilatation.tensorY W (π ^ (k + 1)) b3 b4 b6 K

/-- The full next tensor chart restricts to its original conic boundary. -/
def residueDividedConicMap : T →ₐ[K] B :=
  (residueDividedConicOpenEquiv D k hk b3 b4 b6 h3 h4).toAlgHom.comp
    (IsScalarTower.toAlgHom K T _)

/-- The original tensor horizontal function becomes the inverse conic incidence. -/
theorem residueDividedConicMap_x :
    residueDividedConicMap D k hk b3 b4 b6 h3 h4 tx = (↑(v)⁻¹ : B) := by
  change middleDividedConicOverlap W₀ c h2
    (residueDividedOpenEquiv D k hk b3 b4 b6 h3 h4 (algebraMap T _ tx)) = _
  rw [residueDividedOpenEquiv_base, AlgEquiv.trans_apply,
    WeierstrassDilatation.residueRetainedTensorEquiv_x,
    WeierstrassDilatation.parameterEquiv_x]
  exact middleDividedConicOverlap_x W₀ c h2

/-- The original tensor vertical function keeps its oriented slope ratio. -/
theorem residueDividedConicMap_y :
    residueDividedConicMap D k hk b3 b4 b6 h3 h4 ty =
      (↑(v)⁻¹ : B) * algebraMap C₀ B (conicV (WeierstrassCurve.a₁ W₀) c) := by
  change middleDividedConicOverlap W₀ c h2
    (residueDividedOpenEquiv D k hk b3 b4 b6 h3 h4 (algebraMap T _ ty)) = _
  rw [residueDividedOpenEquiv_base, AlgEquiv.trans_apply,
    WeierstrassDilatation.residueRetainedTensorEquiv_y,
    WeierstrassDilatation.parameterEquiv_y]
  exact middleDividedConicOverlap_y W₀ c h2

/-- The boundary map is the same original middle transition on every tensor function. -/
theorem residueDividedConicMap_transition (z : T) :
    residueMiddleConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4
      (residueMiddleTransition D k hk0 hk b3 b4 b6 h3 h4 (algebraMap T _ z)) =
        residueDividedConicMap D k hk b3 b4 b6 h3 h4 z :=
  residueMiddleTransition_conic D k hk0 hk b3 b4 b6 h3 h4 _

end FLT.Mazur.WeierstrassSuccessiveX
