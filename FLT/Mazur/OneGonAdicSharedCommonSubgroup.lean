/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedSubgroupCoherence
public import FLT.Mazur.OneGonAdicIndependentCommonSubgroup

/-!
# Shared-ring comparisons specialize to the original literal pairwise comparisons

The new arbitrary shared-ring construction retains the original pairwise
finite subgroups and their full compatible comparison by their actual formulas.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s u : Set R)
  (i : (CoefficientStage (base I t ht n s))ᵒᵖ)
  (j : (CoefficientStage (base I t ht n u))ᵒᵖ)
  (hs : complementaryInverse I t ht ∈ s) (hu : complementaryInverse I t ht ∈ u)

variable
  (b : (coefficientModelDiagram (base I t ht n s) (carrier I t ht n s).hom).obj i ⟶
    (integralSmoothOpen (equation (parameter I t ht n s))).toScheme)
  (hb : b ≫ (integralSmoothOpen (equation (parameter I t ht n s))).ι =
    (coefficientModelToInitial (base I t ht n s) (carrier I t ht n s).hom).app i ≫
      embedding I t ht n s)
  (c : (coefficientModelDiagram (base I t ht n u) (carrier I t ht n u).hom).obj j ⟶
    (integralSmoothOpen (equation (parameter I t ht n u))).toScheme)
  (hc : c ≫ (integralSmoothOpen (equation (parameter I t ht n u))).ι =
    (coefficientModelToInitial (base I t ht n u) (carrier I t ht n u).hom).app j ≫
      embedding I t ht n u)

variable
  (hφs : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) s))
  (hφu : Function.Surjective (OneGonFiniteCoefficientCoordinates.modelCoordinates t 1
    (canonicalCoordinates I t ht n) u))

local notation "K" => commonBase I t ht n s u i j
local notation "hS" => base_le_common_left I t ht n s u i j
local notation "hU" => base_le_common_right I t ht n s u i j

/-- The shared construction on the pairwise ring is the original left finite subgroup. -/
theorem sharedFiniteSubgroup_common_left :
    sharedFiniteSubgroup I t ht n s K hS i le_sup_left b hb hs hφs =
      commonFiniteSubgroupLeft I t ht n s u i j hs b hb hφs := rfl

/-- The shared construction on the pairwise ring is the original right finite subgroup. -/
theorem sharedFiniteSubgroup_common_right :
    sharedFiniteSubgroup I t ht n u K hU j le_sup_right c hc hu hφu =
      commonFiniteSubgroupRight I t ht n s u i j hu c hc hφu := rfl

/-- The shared full-curve comparison recovers the original pairwise coefficient comparison. -/
theorem sharedCurveIso_common :
    sharedCurveIso I t ht n s u K hS hU hs hu =
      commonCurveIso I t ht n s u i j hs hu := by
  rw [sharedCurveIso_def, commonCurveIso_def]

/-- The entire compatible comparison specializes to the original pairwise subgroup comparison. -/
theorem sharedFiniteSubgroupIso_common :
    sharedFiniteSubgroupIso I t ht n s u K hS hU hs hu i j
      le_sup_left le_sup_right b hb c hc hφs hφu =
        commonFiniteSubgroupIso I t ht n s u i j hs hu b hb c hc hφs hφu := by
  apply GeneralizedEllipticCurve.FiniteSubgroup.CompatibleIso.ext_curve_hom
  exact congrArg Iso.hom (sharedCurveIso_common I t ht n s u i j hs hu)

end FLT.Mazur.OneGonAdicIndependentModel
