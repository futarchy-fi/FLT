/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineComparisonOverlap
public import FLT.Mazur.CyclicCharacteristicAffineEquationCoherence
public import FLT.Mazur.CyclicCharacteristicAffineUniversalComparison
public import FLT.Mazur.GeneralizedComparisonRefinementTransport
public import FLT.Mazur.WeierstrassUniversalComparisonRefinement

/-!
# The actual affine overlap retains the full universal comparison

The named comparison-overlap map pulls back the original normalized-family
comparison to the refined universal comparison, including all automorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassChangeParameter WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficientPresentationIso coefficientModelIso
  comparisonPresentationHom affineComparisonOverlapMap
variable (n : ℕ) [NeZero n] {A B : Type} [CommRing A] [CommRing B]
  (b c : Bool) (q : Spec (.of A) ⟶ normalizedLocus n b)
  (r : Spec (.of A) ⟶ normalizedLocus n c)
  (q' : Spec (.of B) ⟶ normalizedLocus n b) (r' : Spec (.of B) ⟶ normalizedLocus n c)
  (f : A →+* B) (hq : q' = Spec.map (CommRingCat.ofHom f) ≫ q)
  (hr : r' = Spec.map (CommRingCat.ofHom f) ≫ r)
local notation "W" => affineEquation n b q
local notation "V" => affineEquation n c r
local notation "W'" => affineEquation n b q'
local notation "V'" => affineEquation n c r'
local notation "Q'" => EquationRing W' V'
local notation "k" => Spec.map (CommRingCat.ofHom f)
local notation "s" => affineComparisonStructure n b c q r
local notation "s'" => affineComparisonStructure n b c q' r'
local notation "m" => affineComparisonOverlapMap n b c q r q' r' f hq hr
local notation "t" => Spec.map (CommRingCat.ofHom (RingHom.comp (algebraMap B Q') f))
local notation "ht" => Spec.map_comp (CommRingCat.ofHom f)
  (CommRingCat.ofHom (algebraMap B Q'))
local notation "E" => baseChange (normalizedCurve n b) q
local notation "F" => baseChange (normalizedCurve n c) r

/-- The actual named overlap pulls back the complete original universal comparison. -/
theorem affineUniversalComparison_overlap :
    comparisonPullback E F s m t
      ((ht).trans (affineComparisonOverlapMap_structure n b c q r q' r' f hq hr).symm)
      (affineUniversalComparison n b c q r) =
    (E).baseChangeCompEqIso k s' t ht ≪≫
      ((baseChangeFunctor s').mapIso
        ((normalizedCurve n b).baseChangeCompEqIso q k q' hq)).symm ≪≫
        affineUniversalComparison n b c q' r' ≪≫
          (baseChangeFunctor s').mapIso
            ((normalizedCurve n c).baseChangeCompEqIso r k r' hr) ≪≫
              ((F).baseChangeCompEqIso k s' t ht).symm := by
  unfold affineUniversalComparison
  apply comparisonPullback_refine_transport
    (r := coefficientPresentationIso W (affineEquation_discriminant n b q) f W'
      (affineEquation_discriminant n b q') (affineEquation_named_refine n b q q' f hq))
    (q := coefficientPresentationIso V (affineEquation_discriminant n c r) f V'
      (affineEquation_discriminant n c r') (affineEquation_named_refine n c r r' f hr))
  · subst q'
    change affineEquationIso n b (k ≫ q) ≪≫
      (normalizedCurve n b).baseChangeCompIso q k = _
    simpa only [affineModelPullbackIso_eq_presentation] using
      affineEquationIso_refine_iso n b q f
  · subst r'
    change affineEquationIso n c (k ≫ r) ≪≫
      (normalizedCurve n c).baseChangeCompIso r k = _
    simpa only [affineModelPullbackIso_eq_presentation] using
      affineEquationIso_refine_iso n c r f
  · simpa only [affineComparisonOverlapMap_eq_spec, affineComparisonStructure] using
      universalGeneralizedComparison_refine W V W' V'
        (affineEquation_discriminant n b q) (affineEquation_discriminant n c r)
        (affineEquation_discriminant n b q') (affineEquation_discriminant n c r') f
        (affineEquation_named_refine n b q q' f hq)
        (affineEquation_named_refine n c r r' f hr)

end FLT.Mazur.CyclicCharacteristicAtlas
