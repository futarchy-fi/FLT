/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineComparisonScheme
public import FLT.Mazur.WeierstrassUniversalComparisonClassification
public import FLT.Mazur.GeneralizedComparisonPullbackNaturality

/-!
# The normalized affine classifier is the actual universal pullback

The varying comparison is transported to the original normalized full
families. Its pullback along every affine test is exactly the previously
constructed pointwise classifier, retaining all automorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassIntegralChart WeierstrassChangeParameter GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {A : Type} [CommRing A]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)
local notation "W" => affineEquation n b q
local notation "V" => affineEquation n c r
local notation "hW" => affineEquation_discriminant n b q
local notation "hV" => affineEquation_discriminant n c r
local notation "s" => affineComparisonStructure n b c q r

/-- The actual universal full comparison of the unchanged normalized affine families. -/
def affineUniversalComparison :
    ((normalizedCurve n b).baseChange q).baseChange s ≅
      ((normalizedCurve n c).baseChange r).baseChange s :=
  ((baseChangeFunctor s).mapIso (affineEquationIso n b q)).symm ≪≫
    universalGeneralizedComparison W V hW hV ≪≫
      (baseChangeFunctor s).mapIso (affineEquationIso n c r)

variable (B : Type) [CommRing B] [Algebra A B]
  (f : {f : Spec (.of B) ⟶ affineComparisonScheme n b c q r //
    f ≫ affineComparisonStructure n b c q r = Spec.algebraMap A B})
local notation "t" => Spec.algebraMap A B

/-- Restrict the actual universal comparison and recover the original composite base maps. -/
def affineUniversalComparisonOnTest :
    (normalizedCurve n b).baseChange (t ≫ q) ≅
      (normalizedCurve n c).baseChange (t ≫ r) :=
  (normalizedCurve n b).baseChangeCompIso q t ≪≫
    comparisonPullback _ _ s f.val t f.property.symm
      (affineUniversalComparison n b c q r) ≪≫
        ((normalizedCurve n c).baseChangeCompIso r t).symm

/-- The existing affine classifier equals pullback of the actual universal varying comparison. -/
theorem affineComparisonPointEquiv_universal :
    affineComparisonPointEquiv n b c q r B f =
      affineUniversalComparisonOnTest n b c q r B f := by
  unfold affineUniversalComparisonOnTest affineUniversalComparison
  rw [comparisonPullback_natural]
  change affineComparisonPointEquiv n b c q r B f =
    (normalizedCurve n b).baseChangeCompIso q t ≪≫
      (((baseChangeFunctor t).mapIso (affineEquationIso n b q)).symm ≪≫
        universalComparisonOnTest W V hW hV f ≪≫
          (baseChangeFunctor t).mapIso (affineEquationIso n c r)) ≪≫
            ((normalizedCurve n c).baseChangeCompIso r t).symm
  rw [← generalizedComparisonPointEquiv_apply]
  apply Iso.ext
  simp only [affineComparisonPointEquiv, generalizedComparisonPointEquiv,
    Equiv.trans_apply, Iso.isoCongr, Equiv.coe_fn_mk, affineTestEquationIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]
  rfl

/-- Every prescribed original full comparison is obtained from the universal family uniquely. -/
theorem affineUniversalComparisonOnTest_unique
    (e : (normalizedCurve n b).baseChange (t ≫ q) ≅
      (normalizedCurve n c).baseChange (t ≫ r)) :
    ∃! f : {f : Spec (.of B) ⟶ affineComparisonScheme n b c q r // f ≫ s = t},
      affineUniversalComparisonOnTest n b c q r B f = e := by
  simpa only [← affineComparisonPointEquiv_universal] using
    (affineComparisonPointEquiv n b c q r B).bijective.existsUnique e

end FLT.Mazur.CyclicCharacteristicAtlas
