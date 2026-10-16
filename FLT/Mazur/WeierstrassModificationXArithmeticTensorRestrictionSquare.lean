/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorSpectrumExt
public import FLT.Mazur.WeierstrassModificationXArithmeticProjection
public import FLT.Mazur.WeierstrassModificationXArithmeticTensorNodes
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialNodeRestriction

/-!
# Both full initial tensor nodes commute with arithmetic restriction

The original tensor comparison preserves both projections. The full small and
opposite node squares therefore hold in the unchanged arithmetic tensor chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "e₀" => Iso.hom (arithmeticInitialTensorIso π m W s b3 b4 b6)
local notation "e₁" => Iso.hom (arithmeticInitialTensorIso π (m + 1) W s b3 b4 b6)

/-- The original tensor isomorphism retains the integral initial coordinate projection. -/
@[reassoc] theorem arithmeticInitialTensorIso_projection :
    e₀ ≫ TensorOpenChart.projection =
      Spec.map (CommRingCat.ofHom (coefficientMap W s b3 b4 b6 Q₀).toRingHom) :=
  baseChangeEquiv_spec_projection W s b3 b4 b6 Q₀

/-- Both original projections identify the full tensor base-change restriction square. -/
@[reassoc] theorem arithmeticInitialTensorIso_restriction :
    arithmeticInitialRestriction R π m W s b3 b4 b6 ≫ e₁ =
      e₀ ≫ TensorCoefficientMap.spectrum (restriction R π m) := by
  apply TensorOpenChart.spectrum_hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => arithmeticInitialRestriction R π m W s b3 b4 b6 ≫ z)
        (arithmeticInitialTensorIso_structure π (m + 1) W s b3 b4 b6)).trans
      ((arithmeticInitialRestriction_structure W s b3 b4 b6 π m).trans
      ((congrArg (fun z => z ≫ baseRestriction R π m)
        (arithmeticInitialTensorIso_structure π m W s b3 b4 b6)).symm.trans
      ((Category.assoc _ _ _).trans
      ((congrArg (fun z => e₀ ≫ z)
        (TensorCoefficientMap.spectrum_structure
          (A := Coordinate W s b3 b4 b6) (restriction R π m))).symm.trans
      (Category.assoc _ _ _).symm)))))
  · rw [Category.assoc, arithmeticInitialTensorIso_projection,
      arithmeticInitialRestriction_projection, Category.assoc,
      TensorCoefficientMap.spectrum_projection, arithmeticInitialTensorIso_projection]

variable (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)

/-- The full first initial node commutes with the original tensor coefficient restriction. -/
@[reassoc] theorem arithmeticInitialTensorNodeChart_restriction :
    arithmeticInitialNodeRestriction R π m W s ≫
      arithmeticInitialTensorNodeChart π (m + 1) W s b3 b4 b6 ha h2 h3 h4 h6 =
        arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
          TensorCoefficientMap.spectrum (restriction R π m) := by
  unfold arithmeticInitialTensorNodeChart
  rw [← Category.assoc, arithmeticInitialNodeChart_restriction,
    Category.assoc, arithmeticInitialTensorIso_restriction, Category.assoc]

/-- The full opposite initial node follows the same original tensor restriction. -/
@[reassoc] theorem arithmeticOppositeInitialTensorNodeChart_restriction :
    arithmeticInitialNodeRestriction R π m W s ≫
      arithmeticOppositeInitialTensorNodeChart π (m + 1) W s b3 b4 b6 ha h2 h3 h4 h6 =
        arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
          TensorCoefficientMap.spectrum (restriction R π m) := by
  unfold arithmeticOppositeInitialTensorNodeChart
  rw [← Category.assoc, arithmeticOppositeInitialNodeChart_restriction,
    Category.assoc, arithmeticInitialTensorIso_restriction, Category.assoc]

end FLT.Mazur.WeierstrassModificationX
