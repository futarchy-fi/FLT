/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueIntegralNormalization

/-!
# The retained residue transition is the integral overlap base change

The normalized residue construction agrees with tensoring the original
integral depth overlap. Equality holds on the entire localized tensor
algebra, so every original function and contraction square is retained.
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
local notation "e" => residueMiddleOpenEquiv D k hk0 hk b3 b4 b6 h3 h4
local notation "m" => residueMiddleTransition D k hk0 hk b3 b4 b6 h3 h4
local notation "a₀" => xOpenUnit W₀ 0 0 0 0 c

/-- The normalized horizontal residue substitution has the original inverse-incidence value. -/
theorem residueMiddleTransition_normalized_x :
    e (m (algebraMap T _ (WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K))) =
      (↑a₀⁻¹ : XOpen W₀ 0 0 0 0 c) := by
  rw [residueMiddleTransition_square, residueDividedOpenEquiv_base]
  simp only [AlgEquiv.trans_apply, WeierstrassDilatation.residueRetainedTensorEquiv_x,
    WeierstrassDilatation.parameterEquiv_x]
  change overlapForward W₀ 0 0 0 0 c (algebraMap _ _ _) = _
  rw [overlapForward_base]
  exact dividedOverlapMap_x _ _ _ _ _ _ _ _ _

/-- The normalized vertical residue substitution has the original slope/incidence value. -/
theorem residueMiddleTransition_normalized_y :
    e (m (algebraMap T _ (WeierstrassDilatation.tensorY W (π ^ (k + 1)) b3 b4 b6 K))) =
      (↑a₀⁻¹ : XOpen W₀ 0 0 0 0 c) * algebraMap _ _ (coord W₀ 0 0 0 0 c 1) := by
  rw [residueMiddleTransition_square, residueDividedOpenEquiv_base]
  simp only [AlgEquiv.trans_apply, WeierstrassDilatation.residueRetainedTensorEquiv_y,
    WeierstrassDilatation.parameterEquiv_y]
  change overlapForward W₀ 0 0 0 0 c (algebraMap _ _ _) = _
  rw [overlapForward_base]
  exact dividedOverlapMap_y _ _ _ _ _ _ _ _ _

/-- The retained residue transition is exactly the base change of the integral depth overlap. -/
theorem residueMiddleTransition_eq_integral :
    m = residueIntegralTransition W π k b3 b4 b6 := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IsLocalization.algHom_ext
    (Submonoid.powers (WeierstrassDilatation.tensorX W (π ^ (k + 1)) b3 b4 b6 K))
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassDilatation.hom_ext
  · apply AlgEquiv.injective e
    exact (residueMiddleTransition_normalized_x D k hk0 hk b3 b4 b6 h3 h4).trans
      (residueIntegralTransition_normalized_x D k hk0 hk b3 b4 b6 h3 h4).symm
  · apply AlgEquiv.injective e
    exact (residueMiddleTransition_normalized_y D k hk0 hk b3 b4 b6 h3 h4).trans
      (residueIntegralTransition_normalized_y D k hk0 hk b3 b4 b6 h3 h4).symm

/-- Every original integral overlap function retains its actual restriction square. -/
theorem residueMiddleTransition_integral_coefficient (z : DepthDividedOpen W π k b3 b4 b6) :
    m (PrincipalOpenTensor.coefficient K
      (WeierstrassDilatation.x W (π ^ (k + 1)) b3 b4 b6) z) =
        PrincipalOpenTensor.coefficient K (coord W (π ^ k) π b3 b4 b6 0)
          (depthOverlapEquiv W π k b3 b4 b6 z) := by
  rw [residueMiddleTransition_eq_integral]
  exact residueIntegralTransition_coefficient W π k b3 b4 b6 z

end FLT.Mazur.WeierstrassSuccessiveX
