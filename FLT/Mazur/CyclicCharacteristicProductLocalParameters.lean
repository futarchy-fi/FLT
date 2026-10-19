/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductAffineSchemeTests
public import FLT.Mazur.AffineMorphismTestCover

/-!
# Actual local parameter maps for an arbitrary original-family comparison

An arbitrary test scheme is covered by affine tests over affine product opens.
Each restricted full comparison constructs its unique parameter map. Neither
local parameter maps nor their recovery are supplied as assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool) {T : Scheme}
  (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c)
local notation "p" => prod.lift q r
local notation "C" => AffineMorphismTestCover.cover p
local notation "U" i => AffineMorphismTestCover.targetOpen p i
local notation "t" i => AffineMorphismTestCover.toSpectrum p i
local notation "L" i => productOpenLeft n b c (U i)
local notation "R" i => productOpenRight n b c (U i)

/-- The affine test's left base map is the restriction of the given original base map. -/
theorem productLocalTest_left (i : (C).I₀) : (t i) ≫ (L i) = (C).f i ≫ q := by
  calc
    _ = (((t i) ≫ (U i).1.toScheme.isoSpec.inv) ≫ (U i).1.ι) ≫ prod.fst := by
      simp only [productOpenLeft, DirectedAffineSpectrum.chart, Category.assoc]
    _ = _ := by rw [AffineMorphismTestCover.toSpectrum_base, Category.assoc, prod.lift_fst]

/-- The affine test's right base map is the restriction of the given original base map. -/
theorem productLocalTest_right (i : (C).I₀) : (t i) ≫ (R i) = (C).f i ≫ r := by
  calc
    _ = (((t i) ≫ (U i).1.toScheme.isoSpec.inv) ≫ (U i).1.ι) ≫ prod.snd := by
      simp only [productOpenRight, DirectedAffineSpectrum.chart, Category.assoc]
    _ = _ := by rw [AffineMorphismTestCover.toSpectrum_base, Category.assoc, prod.lift_snd]

variable (e : (normalizedCurve n b).baseChange q ≅ (normalizedCurve n c).baseChange r)

/-- Restrict the prescribed full comparison to the actual affine source test. -/
def productLocalTestComparison (i : (C).I₀) :
    (normalizedCurve n b).baseChange ((t i) ≫ (L i)) ≅
      (normalizedCurve n c).baseChange ((t i) ≫ (R i)) :=
  comparisonPullbackBetween (normalizedCurve n b) (normalizedCurve n c) q r ((C).f i)
    ((t i) ≫ (L i)) ((t i) ≫ (R i)) (productLocalTest_left n b c q r i)
    (productLocalTest_right n b c q r i) e

/-- The restricted original-family comparison determines exactly one local parameter map. -/
theorem productLocalParameter_existsUnique (i : (C).I₀) :
    ∃! k : {k : (C).X i ⟶ productComparisonScheme n b c //
        k ≫ productComparisonStructure n b c =
          ((t i) ≫ (U i).1.toScheme.isoSpec.inv) ≫ (U i).1.ι},
      productSpectrumTestComparison n b c (U i) (t i) k =
        productLocalTestComparison n b c q r e i :=
  productAffineSchemeComparison_unique n b c (U i) (t i)
    (productLocalTestComparison n b c q r e i)

/-- The actual local parameter, constructed from the restricted full comparison. -/
def productLocalParameter (i : (C).I₀) : (C).X i ⟶ productComparisonScheme n b c :=
  (productLocalParameter_existsUnique n b c q r e i).choose.val

/-- Every constructed parameter lies over the original morphism into the product. -/
theorem productLocalParameter_base (i : (C).I₀) :
    productLocalParameter n b c q r e i ≫ productComparisonStructure n b c =
      (C).f i ≫ p :=
  (productLocalParameter_existsUnique n b c q r e i).choose.property.trans
    (AffineMorphismTestCover.toSpectrum_base p i)

/-- The constructed local parameter recovers the prescribed restricted full comparison. -/
theorem productLocalParameter_recovers (i : (C).I₀) :
    productSpectrumTestComparison n b c (U i) (t i)
        (productLocalParameter_existsUnique n b c q r e i).choose =
      productLocalTestComparison n b c q r e i :=
  (productLocalParameter_existsUnique n b c q r e i).choose_spec.1

end FLT.Mazur.CyclicCharacteristicAtlas
