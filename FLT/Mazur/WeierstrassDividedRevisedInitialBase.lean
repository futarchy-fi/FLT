/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInitialMaps
public import FLT.Mazur.WeierstrassDividedRevisedTargetBase

/-!
# Base compatibility of the complete original initial opens

The factor-ratio maps and both original tensor inclusions have the same
coefficient projection, at every arithmetic order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- Both retained orientations preserve the actual smoothing chart's base. -/
@[reassoc] theorem twistedRetainedOrientation_base (b : Bool) :
    (twistedRetainedOrientation data H m b).hom ≫ chartStructure Q τ =
      chartStructure Q τ := by
  cases b <;> simp only [twistedRetainedOrientation, Bool.false_eq_true, ↓reduceIte,
    Iso.refl_hom, Category.id_comp, retainedPolygonSwap_base]

variable (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "L" => PolynomialNodeOpen (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))

/-- The complete original factor-ratio initial map preserves every coefficient. -/
@[reassoc] theorem arithmeticOriginalRevisedInitialMap_base (b : Bool) :
    arithmeticOriginalRevisedInitialMap data H m j hj u hu b ≫
      arithmeticRevisedPolygonToBase data H m j hj u hu =
        Spec.map (CommRingCat.ofHom (algebraMap Q L)) := by
  rw [arithmeticOriginalRevisedInitialMap, Category.assoc, Category.assoc,
    arithmeticRevisedPolygonInitialChart_base, twistedRetainedOrientation_base]
  exact arithmeticInitialFactorRatioChart_structure ..

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0)

/-- The original labeled initial inclusions have the same full coefficient projection. -/
@[reassoc] theorem arithmeticLabeledInitialChart_base (b : Bool) :
    arithmeticLabeledInitialChart hπ data H m (j + 1) hj b ≫
      finiteGlobalArithmeticStructure hπ data (j + 1) hj m =
        Spec.map (CommRingCat.ofHom (algebraMap Q L)) := by
  rw [arithmeticLabeledInitialChart, Category.assoc,
    finiteArithmeticInitialTensorChart_structure]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact arithmeticInitialTensorNodeChart_structure ..
  · exact arithmeticOppositeInitialTensorNodeChart_structure ..

end FLT.Mazur.WeierstrassDividedDepth
