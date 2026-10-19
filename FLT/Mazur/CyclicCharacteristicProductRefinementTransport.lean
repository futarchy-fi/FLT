/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicProductUniversalCharts
public import FLT.Mazur.CyclicCharacteristicAffineOriginalSubgroupOverlap
public import FLT.Mazur.CompatibleParameterRefinementProjection
public import FLT.Mazur.GeneralizedCurveSquareProjection
public import FLT.Mazur.GeneralizedCurveCoverRefinement

/-!
# Coherence of the concrete product chart transports

The original-family chart identifications commute with the actual affine-open
refinements, including their compatible finite subgroups.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassChangeParameter GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] affineComparisonOverlapMap
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "C" => Scheme.Cover.RelativeGluingData.cover (productComparisonGluing n b c)
local notation "L" => productOpenLeft n b c
local notation "R" => productOpenRight n b c
variable {U V : (normalizedProduct n b c).affineOpens} (h : U ⟶ V)
local notation "f" => DirectedAffineSpectrum.restriction (normalizedProduct n b c) (leOfHom h)
local notation "k" => Spec.map (CommRingCat.ofHom f)
local notation "s" => affineComparisonStructure n b c (L V) (R V)
local notation "s'" => affineComparisonStructure n b c (L U) (R U)
local notation "m" => productOpenComparisonMap n b c (leOfHom h)
local notation "Q'" => EquationRing
  (affineEquation n b (A := DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) (L U))
  (affineEquation n c (A := DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) (R U))
local notation "t" => Spec.map (CommRingCat.ofHom
  (RingHom.comp (algebraMap (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) Q') f))
local notation "ht" => Spec.map_comp (CommRingCat.ofHom f)
  (CommRingCat.ofHom (algebraMap (DirectedAffineSpectrum.Ring (normalizedProduct n b c) U) Q'))
local notation "hp" => Eq.trans ht (Eq.symm (affineComparisonOverlapMap_structure n b c
  (L V) (R V) (L U) (R U) f (productOpenLeft_refine n b c (leOfHom h))
    (productOpenRight_refine n b c (leOfHom h))))

/-- The cover transition is the original named parameter overlap map. -/
theorem productComparisonCover_trans : (C).trans h = m := rfl

/-- The actual compatible left endpoint refinement on comparison parameter schemes. -/
def productComparisonLeftRefinement :
    CompatibleIso (((normalizedSubgroup n b).baseChange (L U)).baseChange s')
      ((((normalizedSubgroup n b).baseChange (L V)).baseChange s).baseChange m) :=
  compatibleParameterRefinement s m k s' t hp ht
    (compatibleBaseChangeCompEq (normalizedSubgroup n b) (L V) k (L U)
      (productOpenLeft_refine n b c (leOfHom h)))

/-- The actual compatible right endpoint refinement on comparison parameter schemes. -/
def productComparisonRightRefinement :
    CompatibleIso (((normalizedSubgroup n c).baseChange (R U)).baseChange s')
      ((((normalizedSubgroup n c).baseChange (R V)).baseChange s).baseChange m) :=
  compatibleParameterRefinement s m k s' t hp ht
    (compatibleBaseChangeCompEq (normalizedSubgroup n c) (R V) k (R U)
      (productOpenRight_refine n b c (leOfHom h)))

/-- The full left chart transport commutes with the original cover refinement. -/
theorem productComparisonLeftChartIso_refine :
    productComparisonLeftChartIso n b c U ≪≫ (productComparisonLeftRefinement n b c h).curve =
      coverRefinementIso C (productComparisonLeftCurve n b c) h ≪≫
        (baseChangeFunctor m).mapIso (productComparisonLeftChartIso n b c V) := by
  exact (normalizedCurve n b).baseChangeSquareIso_refine
    (productComparisonStructure n b c ≫ prod.fst) ((C).f U) ((C).f V) m
    (L V) s (L U) s' (productComparisonLeftChart_base n b c U)
    (productComparisonLeftChart_base n b c V) ((C).trans_map h).symm
    (productComparisonLeftRefinement n b c h).curve
    (compatibleParameterRefinement_original_curve_fst (normalizedSubgroup n b)
      (L V) (L U) k (productOpenLeft_refine n b c (leOfHom h)) s m s' t hp ht)

/-- The full right chart transport commutes with the original cover refinement. -/
theorem productComparisonRightChartIso_refine :
    productComparisonRightChartIso n b c U ≪≫ (productComparisonRightRefinement n b c h).curve =
      coverRefinementIso C (productComparisonRightCurve n b c) h ≪≫
        (baseChangeFunctor m).mapIso (productComparisonRightChartIso n b c V) := by
  exact (normalizedCurve n c).baseChangeSquareIso_refine
    (productComparisonStructure n b c ≫ prod.snd) ((C).f U) ((C).f V) m
    (R V) s (R U) s' (productComparisonRightChart_base n b c U)
    (productComparisonRightChart_base n b c V) ((C).trans_map h).symm
    (productComparisonRightRefinement n b c h).curve
    (compatibleParameterRefinement_original_curve_fst (normalizedSubgroup n c)
      (R V) (R U) k (productOpenRight_refine n b c (leOfHom h)) s m s' t hp ht)

end FLT.Mazur.CyclicCharacteristicAtlas
