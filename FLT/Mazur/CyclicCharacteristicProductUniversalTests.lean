/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductUniversalComparison
public import FLT.Mazur.GeneralizedComparisonSquareTest

/-!
# Recovering original comparisons from the global universal family

Tests of the global comparison scheme pull back its full universal comparison.
On each affine chart this recovers the original affine classifier exactly.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "s" => productComparisonStructure n b c
local notation "C" => productComparisonCover n b c

/-- Pull back the actual global universal comparison to the original families on a test. -/
def productUniversalComparisonOnTest {T : Scheme} (f : T ⟶ productComparisonScheme n b c)
    (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
    (hq : q = f ≫ (s ≫ prod.fst)) (hr : r = f ≫ (s ≫ prod.snd)) :
    (normalizedCurve n b).baseChange q ≅ (normalizedCurve n c).baseChange r :=
  comparisonPullbackBetween (normalizedCurve n b) (normalizedCurve n c)
    (s ≫ prod.fst) (s ≫ prod.snd) f q r hq hr (productUniversalComparison n b c)

variable (U : (normalizedProduct n b c).affineOpens)
local notation "L" => productOpenLeft n b c U
local notation "R" => productOpenRight n b c U
local notation "v" => affineComparisonStructure n b c L R

/-- A chart test recovers the local full universal comparison with its original base maps. -/
theorem productUniversalComparisonOnTest_chart {T : Scheme}
    (k : T ⟶ affineComparisonScheme n b c L R)
    (t : T ⟶ Spec (.of (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U)))
    (ht : t = k ≫ v) :
    productUniversalComparisonOnTest n b c (k ≫ (C).f U) (t ≫ L) (t ≫ R)
        (squareTest_base _ _ _ _ (productComparisonLeftChart_base n b c U) k t ht)
        (squareTest_base _ _ _ _ (productComparisonRightChart_base n b c U) k t ht) =
      (normalizedCurve n b).baseChangeCompIso L t ≪≫
        comparisonPullback ((normalizedCurve n b).baseChange L)
          ((normalizedCurve n c).baseChange R) v k t ht
          (affineUniversalComparison n b c L R) ≪≫
        ((normalizedCurve n c).baseChangeCompIso R t).symm := by
  exact comparisonPullbackBetween_chart (normalizedCurve n b) (normalizedCurve n c)
    (s ≫ prod.fst) (s ≫ prod.snd) ((C).f U) L R v
    (productComparisonLeftChart_base n b c U) (productComparisonRightChart_base n b c U)
    k t ht (productUniversalComparison n b c) (affineUniversalComparison n b c L R)
    (productUniversalComparison_chart n b c U)

variable (B : Type) [CommRing B]
  [Algebra (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) B]
local notation "t" => Spec.algebraMap (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) B

/-- The affine classifier is the restriction of the glued full universal comparison. -/
theorem productUniversalComparisonOnTest_affine
    (k : {k : Spec (.of B) ⟶ affineComparisonScheme n b c L R // k ≫ v = t}) :
    productUniversalComparisonOnTest n b c (k.val ≫ (C).f U) (t ≫ L) (t ≫ R)
        (squareTest_base _ _ _ _ (productComparisonLeftChart_base n b c U) _ _ k.property.symm)
        (squareTest_base _ _ _ _ (productComparisonRightChart_base n b c U) _ _ k.property.symm) =
      affineComparisonPointEquiv (A := DirectedAffineSpectrum.Ring (normalizedProduct n b c) U)
        n b c L R B k := by
  rw [productUniversalComparisonOnTest_chart, affineComparisonPointEquiv_universal]
  rfl

end FLT.Mazur.CyclicCharacteristicAtlas
