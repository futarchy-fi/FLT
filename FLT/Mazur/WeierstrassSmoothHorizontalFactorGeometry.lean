/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalCyclicParameter

/-!
# Geometric factor order on the original residue action source

The spectrum of tensor interchange has smooth parameter first and conic
parameter second. Its projections retain the original functions and the
actual reciprocal cyclic parameter map.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
open WeierstrassDividedDepth
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "P" => SmoothYParameterRing D
local notation "C" => SmoothHorizontalResidueRing D
local notation "l" => (Algebra.TensorProduct.includeLeft : P →ₐ[K] P ⊗[K] L)
local notation "r" => (Algebra.TensorProduct.includeRight : L →ₐ[K] P ⊗[K] L)

/-- The original conic-first source viewed with the smooth factor first. -/
def smoothHorizontalResidueInterchangeIso : Spec (.of (P ⊗[K] L)) ≅ Spec (.of C) :=
  Scheme.Spec.mapIso (smoothHorizontalResidueInterchange D).toRingEquiv.toCommRingCatIso.op

/-- Its conic projection is exactly the second-factor projection. -/
theorem smoothHorizontalResidueInterchangeIso_conic :
    (smoothHorizontalResidueInterchangeIso D).hom ≫
        Spec.map (CommRingCat.ofHom (smoothHorizontalResidueConic D).toRingHom) =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom r)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

/-- Its smooth projection is exactly the first-factor projection. -/
theorem smoothHorizontalResidueInterchangeIso_parameter :
    (smoothHorizontalResidueInterchangeIso D).hom ≫
        Spec.map (CommRingCat.ofHom (smoothHorizontalResidueParameter D).toRingHom) =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom l)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1

/-- The cyclic action parameter comes from the smooth first factor after interchange. -/
theorem smoothHorizontalResidueInterchangeIso_cyclic :
    (smoothHorizontalResidueInterchangeIso D).hom ≫
        Spec.map (CommRingCat.ofHom (smoothHorizontalLaurentEvaluation D
          (smoothHorizontalTangentUnit D)⁻¹).toRingHom) =
      Spec.map (CommRingCat.ofHom (AlgHom.toRingHom l)) ≫ smoothYParameterCyclicMap D := by
  rw [smoothHorizontalCyclicParameter_evaluation, smoothHorizontalCyclicParameter_spec,
    ← Category.assoc, smoothHorizontalResidueInterchangeIso_parameter]

end FLT.Mazur.WeierstrassIntegralChart
