/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorSpectrumExt
public import FLT.Mazur.WeierstrassSuccessiveArithmeticProjection
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorBranches
public import FLT.Mazur.WeierstrassSuccessiveArithmeticOppositeRestrictionSquare

/-!
# Full successive tensor branch squares under quotient restriction

The original base-change comparison commutes with the tensor coefficient map.
Both independently constructed polygon branches therefore retain the entire
original tensor chart at consecutive arithmetic orders.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
open PolygonArithmeticStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "Q₀" => Quotient R π m
local notation "Q₁" => Quotient R π (m + 1)
local notation "e₀" => Spec.map (CommRingCat.ofHom
  (RingEquiv.toRingHom
    (AlgEquiv.toRingEquiv (baseChangeEquiv W s π b3 b4 b6 Q₀))))
local notation "e₁" => Spec.map (CommRingCat.ofHom
  (RingEquiv.toRingHom
    (AlgEquiv.toRingEquiv (baseChangeEquiv W s π b3 b4 b6 Q₁))))

/-- The whole base-change spectrum comparison retains the quotient coefficient projection. -/
@[reassoc] theorem arithmeticSuccessiveTensorIso_structure :
    e₀ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Q₀ (ScalarExtension W s π b3 b4 b6 Q₀))) =
        Spec.map (CommRingCat.ofHom
          (algebraMap Q₀ (ExtendedCoordinate W s π b3 b4 b6 Q₀))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (baseChangeEquiv W s π b3 b4 b6 Q₀).toAlgHom.comp_algebraMap

/-- Both original projections identify the full tensor base-change restriction square. -/
@[reassoc] theorem arithmeticSuccessiveTensorIso_restriction :
    arithmeticSuccessiveRestriction R π m W s b3 b4 b6 ≫ e₁ =
      e₀ ≫ TensorCoefficientMap.spectrum (restriction R π m) := by
  apply TensorOpenChart.spectrum_hom_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => arithmeticSuccessiveRestriction R π m W s b3 b4 b6 ≫ z)
        (arithmeticSuccessiveTensorIso_structure π (m + 1) W s b3 b4 b6)).trans
      ((arithmeticSuccessiveRestriction_structure W s π b3 b4 b6 m).trans
      ((congrArg (fun z => z ≫ baseRestriction R π m)
        (arithmeticSuccessiveTensorIso_structure π m W s b3 b4 b6)).symm.trans
      ((Category.assoc _ _ _).trans
      ((congrArg (fun z => e₀ ≫ z)
        (TensorCoefficientMap.spectrum_structure
          (A := Coordinate W s π b3 b4 b6) (restriction R π m))).symm.trans
      (Category.assoc _ _ _).symm)))))
  · rw [Category.assoc, baseChangeEquiv_spec_projection,
      arithmeticSuccessiveRestriction_projection, Category.assoc,
      TensorCoefficientMap.spectrum_projection, baseChangeEquiv_spec_projection]

variable (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
  (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)

/-- Both labels commute with the actual full tensor quotient restriction. -/
@[reassoc] theorem arithmeticTensorBranchChart_restriction (opposite : Bool) :
    arithmeticPolygonNodeRestriction R π m ≫
      arithmeticTensorBranchChart π (m + 1) W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite =
        arithmeticTensorBranchChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 opposite ≫
          TensorCoefficientMap.spectrum (restriction R π m) := by
  cases opposite
  · simp only [arithmeticTensorBranchChart, Bool.false_eq_true, ↓reduceIte]
    rw [← Category.assoc, arithmeticNodeChart_restriction_square,
      Category.assoc, arithmeticSuccessiveTensorIso_restriction π m W s b3 b4 b6,
      Category.assoc]
  · simp only [arithmeticTensorBranchChart, ↓reduceIte]
    rw [← Category.assoc, arithmeticOppositeNodeChart_restriction_square,
      Category.assoc, arithmeticSuccessiveTensorIso_restriction π m W s b3 b4 b6,
      Category.assoc]

end FLT.Mazur.WeierstrassSuccessiveX
