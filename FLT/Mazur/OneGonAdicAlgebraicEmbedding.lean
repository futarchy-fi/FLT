/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicFiniteCoefficientBase

/-!
# Algebraizing the full closed canonical character embedding

The actual canonical closed subscheme descends to a finite-presentation base.
Its source is the same rank-n character scheme, and its whole-cubic Cartesian
square recovers the original canonical embedding and full ideal sheaf.
Smooth-group factorization and the descended cyclic level are not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart OneGonFiniteCoefficientCoordinates
open CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The original rank-n character scheme over the finite coefficient base. -/
abbrev algebraicCarrier : Over (Spec (.of (algebraicBase I t ht n))) :=
  model (algebraicBase I t ht n) (ZMod n)

/-- The actual descended closed embedding into the entire generalized model curve. -/
def algebraicEmbedding : (algebraicCarrier I t ht n).left ⟶
    (algebraicCurve I t ht n).curve.left :=
  modelCurveMap t 1 (canonicalCoordinates I t ht n) (algebraicSupport I t ht n)

/-- The embedding retains the selected coefficient structure morphism. -/
@[reassoc] theorem algebraicEmbedding_structure :
    algebraicEmbedding I t ht n ≫ (algebraicCurve I t ht n).curve.hom =
      (algebraicCarrier I t ht n).hom :=
  modelCurveMap_structure _ _ _ _

/-- The model map is a closed immersion in the whole original model cubic. -/
instance algebraicEmbedding_isClosedImmersion :
    IsClosedImmersion (algebraicEmbedding I t ht n) :=
  modelCurveMap_isClosedImmersion t 1 _ _ (algebraicCoordinates_surjective I t ht n)

/-- The model source has the actual constant rank n in every characteristic. -/
theorem algebraicCarrier_degree :
    FCurve.FiniteLocallyFreeDegree (algebraicCarrier I t ht n).hom n :=
  RootsOfUnityScheme.degree _ n

/-- The whole-cubic projection from the complete base to the finite coefficient model. -/
def algebraicProjection :
    (ArithmeticOneGonGeneralizedCurve.curve t (complementaryFactor_isUnit I t ht)).curve.left ⟶
      (algebraicCurve I t ht n).curve.left :=
  modelCurveProjection t 1 (canonicalCoordinates I t ht n) (algebraicSupport I t ht n)

/-- The original canonical map is exactly the morphism given by its full coordinates. -/
theorem canonical_curveMap_coordinates :
    (canonicalFiniteSubgroup I t ht n).curveMap.left =
      coordinateCurveMap t 1 (canonicalCoordinates I t ht n) := by
  change (effectiveFiniteSubgroup I t ht n (initialRootsHom n I t ht)).curveMap.left = _
  rw [effectiveFiniteSubgroup_curveMap, effectiveSmooth_inclusion]
  rfl

/-- The full canonical embedding is the Cartesian recovery of the constructed model. -/
theorem algebraicEmbedding_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom
      (modelInclusion t 1 (canonicalCoordinates I t ht n) (algebraicSupport I t ht n))))
      (canonicalFiniteSubgroup I t ht n).curveMap.left
      (algebraicEmbedding I t ht n) (algebraicProjection I t ht n) := by
  rw [canonical_curveMap_coordinates]
  exact modelCurveMap_isPullback t 1 _ _

/-- The full original canonical ideal is the pullback of the full algebraic model ideal. -/
theorem algebraicEmbedding_ideal :
    (canonicalFiniteSubgroup I t ht n).ideal =
      (algebraicEmbedding I t ht n).ker.comap (algebraicProjection I t ht n) := by
  change (canonicalFiniteSubgroup I t ht n).curveMap.left.ker = _
  rw [canonical_curveMap_coordinates]
  exact modelCurveMap_ker t 1 _ _ (algebraicCoordinates_surjective I t ht n)

end FLT.Mazur.OneGonAdicCharacterTower
