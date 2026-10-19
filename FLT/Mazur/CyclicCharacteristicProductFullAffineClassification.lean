/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductUniversalTests
public import FLT.Mazur.CyclicCharacteristicProductChartTests

/-!
# Full affine classification by the global universal comparison

The affine point equivalence uses actual maps into the glued parameter scheme.
Its value is exactly the pullback of the global full universal comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
  (U : (normalizedProduct n b c).affineOpens)
local notation "K" => DirectedAffineSpectrum.Ring (normalizedProduct n b c) U
local notation "L" => productOpenLeft n b c U
local notation "R" => productOpenRight n b c U
local notation "s" => productComparisonStructure n b c
variable (B : Type) [CommRing B] [Algebra (DirectedAffineSpectrum.Ring
  (normalizedProduct n b c) U) B]
local notation "t" => Spec.algebraMap K B

/-- Spectrum coordinates and the actual open chart give the same full comparison tests. -/
def productComparisonChartCoordinateEquiv :
    {k : Spec (.of B) ⟶ affineComparisonScheme n b c L R //
      k ≫ affineComparisonStructure n b c L R = t} ≃
    {k : Spec (.of B) ⟶ productOpenComparison n b c U //
      k ≫ productOpenComparisonStructure n b c U = t ≫ U.1.toScheme.isoSpec.inv} :=
  Equiv.subtypeEquivRight fun k ↦ by
    change k ≫ affineComparisonStructure n b c L R = t ↔
      k ≫ (affineComparisonStructure n b c L R ≫ U.1.toScheme.isoSpec.inv) = _
    rw [← Category.assoc, cancel_mono]

/-- Every global comparison test over this affine base has unique chart coordinates. -/
def productComparisonAffineTestEquiv :
    {k : Spec (.of B) ⟶ affineComparisonScheme n b c L R //
      k ≫ affineComparisonStructure n b c L R = t} ≃
    {k : Spec (.of B) ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι} :=
  (productComparisonChartCoordinateEquiv n b c U B).trans
    (productComparisonChartTestEquiv n b c U (t ≫ U.1.toScheme.isoSpec.inv))

/-- Chart inclusion retains the actual global full-comparison test map. -/
theorem productComparisonAffineTestEquiv_apply
    (k : {k : Spec (.of B) ⟶ affineComparisonScheme n b c L R //
      k ≫ affineComparisonStructure n b c L R = t}) :
    (productComparisonAffineTestEquiv n b c U B k).val =
      k.val ≫ (productComparisonCover n b c).f U := rfl

/-- The full affine classifier on actual maps into the glued parameter scheme. -/
def productComparisonAffinePointEquiv :
    {k : Spec (.of B) ⟶ productComparisonScheme n b c //
      k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι} ≃
    ((normalizedCurve n b).baseChange (t ≫ L) ≅
      (normalizedCurve n c).baseChange (t ≫ R)) :=
  (productComparisonAffineTestEquiv n b c U B).symm.trans
    (affineComparisonPointEquiv (A := K) n b c L R B)

variable (k : {k : Spec (.of B) ⟶ productComparisonScheme n b c //
  k ≫ productComparisonStructure n b c =
    (Spec.algebraMap (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) B ≫
      U.1.toScheme.isoSpec.inv) ≫ U.1.ι})

/-- The global parameter map retains the prescribed original left base map. -/
theorem productComparisonAffineTest_left : t ≫ L = k.val ≫ (s ≫ prod.fst) := by
  rw [← Category.assoc, k.property]
  simp only [productOpenLeft, DirectedAffineSpectrum.chart, Category.assoc]

/-- The global parameter map retains the prescribed original right base map. -/
theorem productComparisonAffineTest_right : t ≫ R = k.val ≫ (s ≫ prod.snd) := by
  rw [← Category.assoc, k.property]
  simp only [productOpenRight, DirectedAffineSpectrum.chart, Category.assoc]

/-- Classification is precisely pullback of the actual global universal full comparison. -/
theorem productComparisonAffinePointEquiv_universal :
    productComparisonAffinePointEquiv n b c U B k =
      productUniversalComparisonOnTest n b c k.val (t ≫ L) (t ≫ R)
        (productComparisonAffineTest_left n b c U B k)
        (productComparisonAffineTest_right n b c U B k) := by
  let f := (productComparisonAffineTestEquiv n b c U B).symm k
  have hf : f.val ≫ (productComparisonCover n b c).f U = k.val :=
    congrArg Subtype.val ((productComparisonAffineTestEquiv n b c U B).apply_symm_apply k)
  have h := productUniversalComparisonOnTest_affine n b c U B f
  simp only [hf] at h
  exact h.symm

/-- Every full original affine comparison has one actual global parameter recovering it. -/
theorem productUniversalComparisonOnAffineTest_unique
    (e : (normalizedCurve n b).baseChange (t ≫ L) ≅
      (normalizedCurve n c).baseChange (t ≫ R)) :
    ∃! k : {k : Spec (.of B) ⟶ productComparisonScheme n b c //
        k ≫ s = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι},
      productUniversalComparisonOnTest n b c k.val (t ≫ L) (t ≫ R)
        (productComparisonAffineTest_left n b c U B k)
        (productComparisonAffineTest_right n b c U B k) = e := by
  simpa only [← productComparisonAffinePointEquiv_universal] using
    (productComparisonAffinePointEquiv n b c U B).bijective.existsUnique e

end FLT.Mazur.CyclicCharacteristicAtlas
