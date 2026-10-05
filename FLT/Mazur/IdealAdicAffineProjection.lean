/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedRing

/-!
# Actual affine ideal-power representatives

The ordinary powers of the affine ideal surject onto the actual graded
quotient sections. Their products agree with the constructed sheaf product.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.CoherentIdealIntersection
open FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
variable (U : X.affineOpens)

/-- The original affine ideal power maps to its actual quotient sections. -/
def affineProjection (n : ℕ) : ↥((I.ideal U) ^ n) →ₗ[Γ(X, U.1)] Piece I U.1 n :=
  ((cokernel.π (idealStep I n)).val.app (.op U.1)).hom.comp
    (idealModuleAffineEquiv (I ^ n) U).symm.toLinearMap

/-- Every actual affine graded section has an ordinary ideal-power representative. -/
lemma affineProjection_surjective (n : ℕ) : Function.Surjective (affineProjection I U n) := by
  have := idealModule_coherent (I ^ n)
  have : (cokernel (idealStep I n)).IsFinitePresentation := idealGraded_coherent I n
  exact (GlobalIdealPower.affine_epi_surjective (cokernel.π (idealStep I n)) U).comp
    (idealModuleAffineEquiv (I ^ n) U).symm.surjective

/-- An ordinary ideal-power element viewed in the full actual graded algebra. -/
def affineHomogeneous (n : ℕ) : ↥((I.ideal U) ^ n) →ₗ[Γ(X, U.1)] Sections I U.1 :=
  (of I U.1 n).comp (affineProjection I U n)

/-- Multiplication of affine representatives is the original product in the coordinate ring. -/
lemma affineProjection_mul (a b : ℕ) (r : ↥((I.ideal U) ^ a)) (s : ↥((I.ideal U) ^ b)) :
    mul I U.1 a b (affineProjection I U a r) (affineProjection I U b s) =
      affineProjection I U (a + b)
        ⟨r.val * s.val, by rw [pow_add]; exact Ideal.mul_mem_mul r.property s.property⟩ := by
  change (idealGradedMul I a b).app U.1
    (ModuleSheafTensor.pure _ _ U.1
      ((cokernel.π (idealStep I a)).app U.1 ((idealModuleAffineEquiv (I ^ a) U).symm r))
      ((cokernel.π (idealStep I b)).app U.1 ((idealModuleAffineEquiv (I ^ b) U).symm s))) = _
  rw [idealGradedMul_pure]
  change (cokernel.π (idealStep I (a + b))).app U.1 _ =
    (cokernel.π (idealStep I (a + b))).app U.1
      ((idealModuleAffineEquiv (I ^ (a + b)) U).symm _)
  apply congrArg ((cokernel.π (idealStep I (a + b))).app U.1)
  apply (idealModuleAffineEquiv (I ^ (a + b)) U).injective
  apply Subtype.ext
  simp only [LinearEquiv.apply_symm_apply]
  rw [idealModuleAffineEquiv_val, idealPowerMul_pure]
  rw [← idealModuleAffineEquiv_val, ← idealModuleAffineEquiv_val]
  simp only [LinearEquiv.apply_symm_apply]

/-- Homogeneous representatives multiply in the actual graded section algebra. -/
lemma affineHomogeneous_mul (a b : ℕ) (r : ↥((I.ideal U) ^ a)) (s : ↥((I.ideal U) ^ b)) :
    affineHomogeneous I U a r * affineHomogeneous I U b s =
      affineHomogeneous I U (a + b)
        ⟨r.val * s.val, by rw [pow_add]; exact Ideal.mul_mem_mul r.property s.property⟩ := by
  change of I U.1 a _ * of I U.1 b _ = of I U.1 (a + b) _
  rw [mul_of, affineProjection_mul]

/-- Degree-zero representatives are the original algebra scalars. -/
lemma affineHomogeneous_zero (r : ↥((I.ideal U) ^ 0)) :
    affineHomogeneous I U 0 r = algebraMap Γ(X, U.1) (Sections I U.1) r.val := by
  change of I U.1 0 ((cokernel.π (idealStep I 0)).app U.1
    ((idealModuleAffineEquiv (I ^ 0) U).symm r)) =
      of I U.1 0 ((cokernel.π (idealStep I 0)).app U.1
        ((idealPowerZeroIso I).inv.app U.1 r.val))
  congr 2
  apply ModuleSubobjectCoverEquality.app_injective (idealModuleι (I ^ 0)) U.1
  rw [idealPowerZeroIso_inv_app, ← idealModuleAffineEquiv_val]
  simp only [LinearEquiv.apply_symm_apply]

end FLT.Mazur.IdealAdicGradedSections
