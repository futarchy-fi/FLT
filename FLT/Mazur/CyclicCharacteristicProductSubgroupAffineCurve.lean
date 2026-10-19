/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductAffineClassification
public import FLT.Mazur.CyclicCharacteristicProductFullAffineClassification
public import FLT.Mazur.CyclicCharacteristicProductSubgroupInclusion

/-!
# The global affine subgroup classifier retains the universal full curve

Forgetting the subgroup condition agrees with the actual closed inclusion
of parameter schemes and with pullback of the glued universal comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
  (U : (normalizedProduct n b c).affineOpens)
local notation "K" => DirectedAffineSpectrum.Ring (normalizedProduct n b c) U
local notation "L" => productOpenLeft n b c U
local notation "R" => productOpenRight n b c U
local notation "i" => productSubgroupInclusion n b c
variable (B : Type) [CommRing B] [Algebra (DirectedAffineSpectrum.Ring
  (normalizedProduct n b c) U) B]
local notation "t" => Spec.algebraMap K B
variable (k : {k : Spec (.of B) ⟶ productSubgroupScheme n b c //
  k ≫ productSubgroupStructure n b c =
    (Spec.algebraMap (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) B ≫
      U.1.toScheme.isoSpec.inv) ≫ U.1.ι})

/-- The actual closed inclusion forgets the subgroup condition on a global affine test. -/
def productSubgroupAffineForget :
    {f : Spec (.of B) ⟶ productComparisonScheme n b c //
      f ≫ productComparisonStructure n b c = (t ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι} :=
  ⟨k.val ≫ i, by rw [Category.assoc, productSubgroupInclusion_structure]; exact k.property⟩

/-- The compatible classifier retains the full comparison of its actual parameter map. -/
theorem productSubgroupAffinePointEquiv_curve_global :
    (productSubgroupAffinePointEquiv n b c U B k).curve =
      productComparisonAffinePointEquiv n b c U B (productSubgroupAffineForget n b c U B k) := by
  let e := (productSubgroupChartCoordinateEquiv n b c U B).trans
    (productSubgroupChartTestEquiv n b c U (t ≫ U.1.toScheme.isoSpec.inv))
  let f := e.symm k
  have hf : f.val ≫ (productSubgroupCover n b c).f U = k.val :=
    congrArg Subtype.val (e.apply_symm_apply k)
  let l := subgroupTestForget (affineSubgroupInclusion n b c L R)
    (affineComparisonStructure n b c L R) t f
  have hl : l.val ≫ (productComparisonCover n b c).f U = k.val ≫ i := by
    change (f.val ≫ affineSubgroupInclusion n b c L R) ≫ _ = _
    rw [Category.assoc, ← productSubgroupInclusion_chart, ← Category.assoc, hf]
  have h := affineSubgroupPointEquiv_curve (A := K) n b c L R B f
  rw [← affineComparisonPointEquiv_universal] at h
  have hu := productUniversalComparisonOnTest_affine n b c U B l
  simp only [hl] at hu
  rw [productComparisonAffinePointEquiv_universal]
  exact h.trans hu.symm

/-- The subgroup classifier's curve is pullback of the global full universal comparison. -/
theorem productSubgroupAffinePointEquiv_universal_curve :
    (productSubgroupAffinePointEquiv n b c U B k).curve =
      productUniversalComparisonOnTest n b c (k.val ≫ i) (t ≫ L) (t ≫ R)
        (productComparisonAffineTest_left n b c U B (productSubgroupAffineForget n b c U B k))
        (productComparisonAffineTest_right n b c U B
          (productSubgroupAffineForget n b c U B k)) := by
  rw [productSubgroupAffinePointEquiv_curve_global, productComparisonAffinePointEquiv_universal]
  rfl

end FLT.Mazur.CyclicCharacteristicAtlas
