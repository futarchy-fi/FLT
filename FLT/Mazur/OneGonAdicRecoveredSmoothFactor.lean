/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicAlgebraicEmbedding
public import FLT.Mazur.OneGonSmoothCoefficientProjection
public import FLT.Mazur.CoefficientFactorizationDescent

/-!
# The canonical smooth factor on the recovered finite coefficient source

The actual complete-base character scheme is identified with the recovery of
the fixed finite coefficient source. Its smooth factor maps to the original
finite coefficient smooth model, with the original whole-cubic composite.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.OneGonAdicCharacterTower

open OneGonSmoothing WeierstrassIntegralChart CharacterSchemeBaseChange Approximation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (t : R) (ht : t ∈ I) (n : ℕ) [NeZero n]

/-- The actual character coefficient projection to the selected algebraic source. -/
def algebraicSourceProjection : (model R (ZMod n)).left ⟶
    (algebraicCarrier I t ht n).left :=
  Spec.map (CommRingCat.ofHom (CharacterAlgebraScalarExtension.coeff
    (algebraicBase I t ht n) R (ZMod n)).toRingHom)

/-- The complete character scheme is the recovery of the fixed finite coefficient source. -/
def algebraicSourceRecovery : (model R (ZMod n)).left ≅
    (coefficientModelCone (algebraicBase I t ht n) (algebraicCarrier I t ht n).hom).pt :=
  (coefficientMap_isPullback (algebraicBase I t ht n) R (ZMod n)).isoPullback

/-- Recovery retains exactly the chosen character coefficient projection. -/
@[reassoc] theorem algebraicSourceRecovery_fst :
    (algebraicSourceRecovery I t ht n).inv ≫ algebraicSourceProjection I t ht n =
      pullback.fst (algebraicCarrier I t ht n).hom
        (Spec.map (CommRingCat.ofHom (algebraicBase I t ht n).val.toRingHom)) :=
  (coefficientMap_isPullback (algebraicBase I t ht n) R (ZMod n)).isoPullback_inv_fst

/-- The original canonical smooth factor, viewed on the recovered model source. -/
def recoveredSmoothFactor :
    (coefficientModelCone (algebraicBase I t ht n) (algebraicCarrier I t ht n).hom).pt ⟶
      (integralSmoothOpen (equation (algebraicParameter I t ht n))).toScheme :=
  (algebraicSourceRecovery I t ht n).inv ≫
    effectiveSmooth I t ht (initialRootsHom n I t ht) ≫
      smoothCoefficientProjection (S := R) (algebraicParameter I t ht n)

/-- The recovered smooth factor has the exact initial algebraic embedding as composite. -/
@[reassoc] theorem recoveredSmoothFactor_inclusion :
    recoveredSmoothFactor I t ht n ≫
      (integralSmoothOpen (equation (algebraicParameter I t ht n))).ι =
        pullback.fst (algebraicCarrier I t ht n).hom
          (Spec.map (CommRingCat.ofHom (algebraicBase I t ht n).val.toRingHom)) ≫
            algebraicEmbedding I t ht n := by
  rw [recoveredSmoothFactor, Category.assoc, Category.assoc,
    smoothCoefficientProjection_inclusion]
  have he := effectiveSmooth_inclusion_assoc I t ht (initialRootsHom n I t ht)
    (coefficientMorphism (S := R) (algebraicParameter I t ht n))
  erw [he]
  have h := (algebraicEmbedding_isPullback I t ht n).w
  rw [canonical_curveMap_coordinates] at h
  change algebraicSourceProjection I t ht n ≫ algebraicEmbedding I t ht n =
    (effectiveAffine I t ht (initialRootsHom n I t ht) ≫
      integralCurveChart (equation t) 1) ≫
        coefficientMorphism (S := R) (algebraicParameter I t ht n) at h
  rw [Category.assoc] at h
  erw [← h]
  rw [← Category.assoc, algebraicSourceRecovery_fst]

/-- The recovered factor is over the initial finite coefficient spectrum. -/
@[reassoc] theorem recoveredSmoothFactor_structure :
    recoveredSmoothFactor I t ht n ≫
      integralSmoothStructure (equation (algebraicParameter I t ht n)) =
        pullback.fst (algebraicCarrier I t ht n).hom
          (Spec.map (CommRingCat.ofHom (algebraicBase I t ht n).val.toRingHom)) ≫
            (algebraicCarrier I t ht n).hom := by
  change _ ≫ (integralSmoothOpen _).ι ≫ _ = _
  rw [recoveredSmoothFactor_inclusion_assoc]
  exact congrArg (fun f => pullback.fst (algebraicCarrier I t ht n).hom
    (Spec.map (CommRingCat.ofHom (algebraicBase I t ht n).val.toRingHom)) ≫ f)
      (algebraicEmbedding_structure I t ht n)

end FLT.Mazur.OneGonAdicCharacterTower
