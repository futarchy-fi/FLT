/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioAffine
public import FLT.Mazur.WeierstrassModificationXArithmeticTensorRestrictionSquare

/-!
# The full affine polygon comparison on the original tensor chart

Transport through the original coefficient isomorphism retains both node
labels, the coefficient structure, and the consecutive arithmetic square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] arithmeticFactorRatioAffinePolygonMap
  arithmeticInitialFactorRatioChart arithmeticInitialNodeChart arithmeticOppositeInitialNodeChart
variable {R : Type} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (hs : π ∣ s)
  (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)
local notation "Q" => Quotient R π m
local notation "e" => arithmeticInitialTensorIso π m W s b3 b4 b6
local notation "τ" => arithmeticInitialMobiusSmoothing W ha s π m
local notation "hn" => Fact.mk (arithmeticInitialFactorRatioSmoothing_nilpotent W ha s π m hs)

/-- The entire original tensor initial chart maps to the corrected arithmetic polygon. -/
def arithmeticFactorRatioTensorAffineMap (k : ℕ) :
    Spec (.of (Q ⊗[R] Coordinate W s b3 b4 b6)) ⟶
      arithmeticFactorRatioPolygon π m W s ha hs k :=
  (e).inv ≫ arithmeticFactorRatioAffinePolygonMap π m W s b3 b4 b6
    ha hs h2 h3 h4 h6 k

/-- Transport recovers the complete affine comparison, on every original function. -/
@[reassoc] theorem arithmeticFactorRatioTensorAffineMap_transport (k : ℕ) :
    (e).hom ≫ arithmeticFactorRatioTensorAffineMap π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 k =
        arithmeticFactorRatioAffinePolygonMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k := by
  rw [arithmeticFactorRatioTensorAffineMap, Iso.hom_inv_id_assoc]

/-- Both full tensor node labels retain the same exact normalization and cyclic indices. -/
@[reassoc] theorem arithmeticFactorRatioTensorAffineMap_chart (k : ℕ) (b : Bool) :
    (if b then arithmeticOppositeInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6
      else arithmeticInitialTensorNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6) ≫
        arithmeticFactorRatioTensorAffineMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k =
      arithmeticInitialFactorRatioChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
        (if b then (branchSwapIso Q τ).hom else 𝟙 _) ≫
          @PolygonInfinitesimal.chart Q _ τ hn (2 * k + 3) (by omega) (initialPolygonIndex k b) :=
  by
    have h := arithmeticFactorRatioAffinePolygonMap_chart π m W s b3 b4 b6
      ha hs h2 h3 h4 h6 k b
    cases b <;> simpa only [Bool.false_eq_true, ↓reduceIte,
      arithmeticInitialTensorNodeChart, arithmeticOppositeInitialTensorNodeChart,
      Category.assoc, arithmeticFactorRatioTensorAffineMap_transport] using h

/-- The original tensor coefficient projection is unchanged by the full comparison. -/
@[reassoc] theorem arithmeticFactorRatioTensorAffineMap_structure (k : ℕ) :
    arithmeticFactorRatioTensorAffineMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k ≫
      @PolygonInfinitesimal.toBase Q _ τ (2 * k + 3) hn (by omega) =
        Spec.map (CommRingCat.ofHom (algebraMap Q (Q ⊗[R] Coordinate W s b3 b4 b6))) := by
  rw [arithmeticFactorRatioTensorAffineMap, Category.assoc,
    arithmeticFactorRatioAffinePolygonMap_structure, ← arithmeticInitialTensorIso_structure,
    Iso.inv_hom_id_assoc]

/-- Consecutive full tensor comparisons follow the actual arithmetic quotient map. -/
@[reassoc] theorem arithmeticFactorRatioTensorAffineMap_restriction (k : ℕ) :
    arithmeticFactorRatioTensorAffineMap π m W s b3 b4 b6 ha hs h2 h3 h4 h6 k ≫
      arithmeticFactorRatioPolygonRestriction π m W s ha hs k =
        TensorCoefficientMap.spectrum (restriction R π m) ≫
          arithmeticFactorRatioTensorAffineMap π (m + 1) W s b3 b4 b6
            ha hs h2 h3 h4 h6 k := by
  apply (cancel_epi (e).hom).mp
  rw [arithmeticFactorRatioTensorAffineMap_transport_assoc,
    arithmeticFactorRatioAffinePolygonMap_restriction,
    ← arithmeticInitialTensorIso_restriction_assoc,
    arithmeticFactorRatioTensorAffineMap_transport]

end FLT.Mazur.WeierstrassDividedDepth
