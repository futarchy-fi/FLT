/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicIndependentBase
public import FLT.Mazur.OneGonAdicAlgebraicEmbedding

/-!
# Whole embeddings for arbitrary canonical coefficient supports

The actual canonical closed subscheme descends to a finite-presentation base.
Its source is the same rank-n character scheme, and its whole-cubic Cartesian
square recovers the original canonical embedding and full ideal sheaf.
Smooth-group factorization and the descended cyclic level are not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicIndependentModel

open OneGonSmoothing WeierstrassIntegralChart OneGonFiniteCoefficientCoordinates
open CharacterSchemeBaseChange OneGonAdicCharacterTower

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n] (s : Set R)

/-- The actual descended closed embedding into the entire generalized model curve. -/
def embedding : (carrier I t ht n s).left ⟶
    integralCurve (equation (parameter I t ht n s)) :=
  modelCurveMap t 1 (canonicalCoordinates I t ht n) s

/-- The embedding retains the selected coefficient structure morphism. -/
@[reassoc] theorem embedding_structure :
    embedding I t ht n s ≫ integralCurveStructure (equation (parameter I t ht n s)) =
      (carrier I t ht n s).hom :=
  modelCurveMap_structure _ _ _ _

/-- The model map is a closed immersion in the whole original model cubic. -/
theorem embedding_isClosedImmersion
    (hφ : Function.Surjective (modelCoordinates t 1 (canonicalCoordinates I t ht n) s)) :
    IsClosedImmersion (embedding I t ht n s) :=
  modelCurveMap_isClosedImmersion t 1 _ _ hφ

/-- The whole-cubic projection from the complete base to the finite coefficient model. -/
def projection :
    (ArithmeticOneGonGeneralizedCurve.curve t (complementaryFactor_isUnit I t ht)).curve.left ⟶
      integralCurve (equation (parameter I t ht n s)) :=
  modelCurveProjection t 1 (canonicalCoordinates I t ht n) s

/-- The full canonical embedding is the Cartesian recovery of the constructed model. -/
theorem embedding_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom
      (modelInclusion t 1 (canonicalCoordinates I t ht n) s)))
      (canonicalFiniteSubgroup I t ht n).curveMap.left
      (embedding I t ht n s) (projection I t ht n s) := by
  rw [canonical_curveMap_coordinates]
  exact modelCurveMap_isPullback t 1 _ _

/-- The full original canonical ideal is the pullback of the full algebraic model ideal. -/
theorem embedding_ideal
    (hφ : Function.Surjective (modelCoordinates t 1 (canonicalCoordinates I t ht n) s)) :
    (canonicalFiniteSubgroup I t ht n).ideal =
      (embedding I t ht n s).ker.comap (projection I t ht n s) := by
  change (canonicalFiniteSubgroup I t ht n).curveMap.left.ker = _
  rw [canonical_curveMap_coordinates]
  exact modelCurveMap_ker t 1 _ _ hφ

end FLT.Mazur.OneGonAdicIndependentModel
