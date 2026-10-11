/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalLaurentEvaluation
public import FLT.Mazur.LaurentUnitPoints

/-!
# Smooth-first order on the actual horizontal residue product

Tensor interchange moves the original conic and smooth inclusions to the
second and first factors, respectively. Laurent evaluation is transported
as a whole algebra map, so inverse powers are retained.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "P" => SmoothYParameterRing D
local notation "C" => SmoothHorizontalResidueRing D

/-- Interchange the two actual residue factors to put the smooth parameter first. -/
def smoothHorizontalResidueInterchange : C ≃ₐ[K] P ⊗[K] L :=
  Algebra.TensorProduct.comm K L P

/-- Every conic function moves to the second factor. -/
theorem smoothHorizontalResidueInterchange_conic (f : L) :
    smoothHorizontalResidueInterchange D (smoothHorizontalResidueConic D f) =
      Algebra.TensorProduct.includeRight f := by
  change Algebra.TensorProduct.comm K L P (f ⊗ₜ[K] 1) = 1 ⊗ₜ[K] f
  exact Algebra.TensorProduct.comm_tmul _ _ _

/-- Every smooth affine parameter function moves to the first factor. -/
theorem smoothHorizontalResidueInterchange_parameter (f : P) :
    smoothHorizontalResidueInterchange D (smoothHorizontalResidueParameter D f) =
      (Algebra.TensorProduct.includeLeft : P →ₐ[K] P ⊗[K] L) f := by
  change Algebra.TensorProduct.comm K L P (1 ⊗ₜ[K] f) = f ⊗ₜ[K] 1
  exact Algebra.TensorProduct.comm_tmul _ _ _

/-- The conic unit after interchange is the second-factor Laurent generator. -/
theorem smoothHorizontalResidueInterchange_conicUnit :
    smoothHorizontalResidueInterchange D (smoothHorizontalConicUnit D : C) =
      Algebra.TensorProduct.includeRight (LaurentPolynomial.T 1) := by
  rw [smoothHorizontalConicUnit_val, smoothHorizontalResidueInterchange_conic]

/-- The smooth tangent unit after interchange is the first-factor Laurent generator. -/
theorem smoothHorizontalResidueInterchange_tangentUnit :
    smoothHorizontalResidueInterchange D (smoothHorizontalTangentUnit D : C) =
      (Algebra.TensorProduct.includeLeft : P →ₐ[K] P ⊗[K] L)
        (algebraMap L P (LaurentPolynomial.T 1)) := by
  rw [smoothHorizontalTangentUnit_val, smoothHorizontalResidueInterchange_parameter]

/-- Whole Laurent evaluation after the actual interchange. -/
def smoothHorizontalOrderedEvaluation (q : (P ⊗[K] L)ˣ) : L →ₐ[K] P ⊗[K] L :=
  { LaurentPolynomial.eval₂ (algebraMap K (P ⊗[K] L)) q with
    commutes' := fun r => LaurentPolynomial.eval₂_C _ _ r }

/-- Interchange transports every Laurent function, including all negative powers. -/
theorem smoothHorizontalResidueInterchange_evaluation (q : Cˣ) :
    (smoothHorizontalResidueInterchange D).toAlgHom.comp
        (smoothHorizontalLaurentEvaluation D q) =
      smoothHorizontalOrderedEvaluation D
        (Units.map (smoothHorizontalResidueInterchange D).toRingEquiv.toRingHom q) := by
  apply LaurentUnitPoints.hom_ext
  all_goals
    change smoothHorizontalResidueInterchange D
      (smoothHorizontalLaurentEvaluation D q (LaurentPolynomial.T _)) = _
    rw [smoothHorizontalLaurentEvaluation_T]
    change smoothHorizontalResidueInterchange D (↑(q ^ _) : C) =
      LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.T _)
    rw [LaurentPolynomial.eval₂_T]
    simp only [← map_zpow, Units.coe_map]
    rfl

end FLT.Mazur.WeierstrassIntegralChart
